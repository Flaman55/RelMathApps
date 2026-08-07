"""
manifest.py -- pure-logic, tkinter-free models for the Ustawienia tab's backup/restore
feature.

A "backup" here is NOT a copy of the actual prime/constellation data -- a single piętro can
be hundreds of GB (see portal_browser_v1.py's own totals-worker comments on per-piętro scan
cost), copying that wholesale is not realistic. A backup is a MANIFEST: a lightweight JSON
snapshot of what SHOULD exist on disk (which piętra, which source-window filenames each,
which constellation k/variant hit files, what each piętro's constellation CHECKPOINT.txt
said) plus a copy of benchmark_log.csv's text. Restoring a backup means comparing this
manifest against the CURRENT disk state and, if anything is missing, optionally
regenerating it via the existing orchestrator_loop_v2.py / constellation_finder_v1.py
pipelines -- see restore_job.py for the checkpointed/pausable job that drives that.
"""
import os
import re
import datetime

_PIETRO_DIR_RE = re.compile(r"^10p(\d+)$")
_SOURCE_WINDOW_RE = re.compile(r"^PRIME_WINDOW_10p\d+_off_(\d+)(M)?\.bin$")
_CONSTELLATION_K_RE = re.compile(r"^k(\d+)$")
_CONSTELLATION_VARIANT_RE = re.compile(r"^variant(\d+)$")
_HITS_FILE_RE = re.compile(r"^HITS_10p\d+_k\d+_v\d+\.bin$")


def _pietra_on_disk(storage_path):
    """Every base_exponent with a 10p{N} folder actually present on disk right now --
    shared by build_from_disk() (what to snapshot) and diff_against_disk() (which also
    needs this to notice a piętro that exists on disk but was never in the backup at
    all -- see that method's docstring)."""
    found = set()
    if os.path.isdir(storage_path):
        for name in os.listdir(storage_path):
            m = _PIETRO_DIR_RE.match(name)
            if m and os.path.isdir(os.path.join(storage_path, name)):
                found.add(int(m.group(1)))
    return found


class PietroSnapshot:
    """What one piętro (10p{N}/source_primes/) looked like on disk at backup time: just
    filenames, not contents -- the filename alone encodes the offset (see
    _SOURCE_WINDOW_RE), and reading every window's header just to build a backup would be
    exactly the expensive per-file I/O the totals-cache background worker already exists to
    avoid (portal_browser_v1.py, ~78s for one 15,101-file piętro). A backup only needs to
    know WHICH files exist -- restoring means regenerating missing ones from scratch, not
    restoring bytes."""

    def __init__(self, base_exponent, filenames):
        self.base_exponent = base_exponent
        self.filenames = sorted(filenames)

    @property
    def file_count(self):
        return len(self.filenames)

    def to_dict(self):
        return {"base_exponent": self.base_exponent, "filenames": self.filenames}

    @classmethod
    def from_dict(cls, data):
        return cls(int(data["base_exponent"]), list(data.get("filenames", [])))

    @classmethod
    def scan(cls, storage_path, base_exponent):
        source_dir = os.path.join(storage_path, f"10p{base_exponent}", "source_primes")
        if not os.path.isdir(source_dir):
            return cls(base_exponent, [])
        names = [n for n in os.listdir(source_dir) if _SOURCE_WINDOW_RE.match(n)]
        return cls(base_exponent, names)

    def missing_from(self, other):
        """Filenames present in self (the backup) but absent from `other` (current disk)."""
        return sorted(set(self.filenames) - set(other.filenames))


class ConstellationSnapshot:
    """What one piętro's constellations/ folder looked like: which (k, variant) hit files
    exist (as "k{K}/variant{V}/HITS_....bin" relative paths), plus the piętro-level
    CHECKPOINT.txt text (constellation_finder_v1.py writes ONE checkpoint per piętro, not
    per k/variant -- see that file's own module docstring)."""

    def __init__(self, base_exponent, hit_files, checkpoint_text):
        self.base_exponent = base_exponent
        self.hit_files = sorted(hit_files)
        self.checkpoint_text = checkpoint_text  # None if no checkpoint existed at scan time

    def to_dict(self):
        return {
            "base_exponent": self.base_exponent,
            "hit_files": self.hit_files,
            "checkpoint_text": self.checkpoint_text,
        }

    @classmethod
    def from_dict(cls, data):
        return cls(int(data["base_exponent"]), list(data.get("hit_files", [])),
                    data.get("checkpoint_text"))

    @classmethod
    def scan(cls, storage_path, base_exponent):
        const_dir = os.path.join(storage_path, f"10p{base_exponent}", "constellations")
        hit_files = []
        if os.path.isdir(const_dir):
            for k_name in os.listdir(const_dir):
                k_path = os.path.join(const_dir, k_name)
                if not _CONSTELLATION_K_RE.match(k_name) or not os.path.isdir(k_path):
                    continue
                for variant_name in os.listdir(k_path):
                    variant_path = os.path.join(k_path, variant_name)
                    if not _CONSTELLATION_VARIANT_RE.match(variant_name) or not os.path.isdir(variant_path):
                        continue
                    for fname in os.listdir(variant_path):
                        if _HITS_FILE_RE.match(fname):
                            hit_files.append(f"{k_name}/{variant_name}/{fname}")
        checkpoint_path = os.path.join(const_dir, "CHECKPOINT.txt")
        checkpoint_text = None
        if os.path.exists(checkpoint_path):
            try:
                with open(checkpoint_path, encoding="utf-8") as f:
                    checkpoint_text = f.read()
            except OSError:
                checkpoint_text = None
        return cls(base_exponent, hit_files, checkpoint_text)

    def missing_from(self, other):
        return sorted(set(self.hit_files) - set(other.hit_files))


class BackupManifest:
    """Full snapshot: every piętro's PietroSnapshot + ConstellationSnapshot, plus a copy of
    benchmark_log.csv's raw text (small -- a few hundred rows even after months of use, see
    portal_browser_v1.py's own Benchmark tab -- safe to embed directly in the manifest JSON
    rather than as a separate file to keep track of)."""

    def __init__(self, timestamp_utc, storage_path, pietra, constellations, benchmark_csv_text):
        self.timestamp_utc = timestamp_utc
        self.storage_path = storage_path
        self.pietra = {p.base_exponent: p for p in pietra}
        self.constellations = {c.base_exponent: c for c in constellations}
        self.benchmark_csv_text = benchmark_csv_text

    @property
    def name(self):
        return f"backup_{self.timestamp_utc}"

    def to_dict(self):
        return {
            "timestamp_utc": self.timestamp_utc,
            "storage_path": self.storage_path,
            "pietra": [p.to_dict() for p in self.pietra.values()],
            "constellations": [c.to_dict() for c in self.constellations.values()],
            "benchmark_csv_text": self.benchmark_csv_text,
        }

    @classmethod
    def from_dict(cls, data):
        return cls(
            data["timestamp_utc"], data.get("storage_path", ""),
            [PietroSnapshot.from_dict(p) for p in data.get("pietra", [])],
            [ConstellationSnapshot.from_dict(c) for c in data.get("constellations", [])],
            data.get("benchmark_csv_text", ""),
        )

    @classmethod
    def build_from_disk(cls, storage_path):
        """Scans storage_path RIGHT NOW and builds a fresh manifest -- this is what
        "Backup" actually does (see backup_store.py.BackupStore.create()). Cheap: only
        os.listdir() calls, no per-file header reads (unlike portal_browser_v1.py's totals-
        cache worker, which needs actual prime counts -- a backup only needs to know WHICH
        files exist)."""
        timestamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        pietra = []
        constellations = []
        for base_exponent in sorted(_pietra_on_disk(storage_path)):
            pietra.append(PietroSnapshot.scan(storage_path, base_exponent))
            constellations.append(ConstellationSnapshot.scan(storage_path, base_exponent))
        csv_path = os.path.join(storage_path, "benchmark_log.csv")
        csv_text = ""
        if os.path.exists(csv_path):
            try:
                with open(csv_path, encoding="utf-8") as f:
                    csv_text = f.read()
            except OSError:
                csv_text = ""
        return cls(timestamp, storage_path, pietra, constellations, csv_text)

    def diff_against_disk(self, storage_path):
        """Compares this manifest against storage_path's CURRENT state. Returns
        {base_exponent: {"missing_windows": [...], "missing_hits": [...],
        "extra_windows": [...], "extra_hits": [...]}} for every piętro that differs in
        EITHER direction -- an empty dict means the backup and the disk match exactly.
        Piętra with nothing missing AND nothing extra are simply absent from the result,
        same reasoning as aggregate_write_seconds_by_pietro() in portal_browser_v1.py only
        including piętra that actually have data.

        The comparison unions self.pietra's keys with EVERY piętro folder actually on
        disk right now (_pietra_on_disk()), and computes BOTH directions for each:
        missing_from() (the backup has it, disk doesn't -- restore_job.py's
        regenerate-it path) and its mirror, current.missing_from(snap) (disk has it,
        backup doesn't -- the extra_windows/extra_hits fields, which the caller can
        offer to delete, always with an explicit confirm/cancel prompt -- see
        restore_job.py's delete_extra_files() and settings_tab.py's
        _on_start_restore()). This also covers a piętro entirely absent from the
        backup (e.g. one added to the magazyn after the backup was taken, with no
        entry in self.pietra at all): its snapshot is treated as empty, so ALL of its
        files come back as extra_windows/extra_hits rather than being silently
        invisible to the diff."""
        result = {}
        all_base_exponents = set(self.pietra.keys()) | _pietra_on_disk(storage_path)
        for base_exponent in all_base_exponents:
            snap = self.pietra.get(base_exponent)
            current = PietroSnapshot.scan(storage_path, base_exponent)
            if snap is not None:
                missing_windows = snap.missing_from(current)
                extra_windows = current.missing_from(snap)
            else:
                missing_windows = []
                extra_windows = list(current.filenames)

            const_snap = self.constellations.get(base_exponent)
            current_const = ConstellationSnapshot.scan(storage_path, base_exponent)
            if const_snap is not None:
                missing_hits = const_snap.missing_from(current_const)
                extra_hits = current_const.missing_from(const_snap)
            else:
                missing_hits = []
                extra_hits = list(current_const.hit_files)

            if missing_windows or missing_hits or extra_windows or extra_hits:
                result[base_exponent] = {
                    "missing_windows": missing_windows,
                    "missing_hits": missing_hits,
                    "extra_windows": extra_windows,
                    "extra_hits": extra_hits,
                }
        return result
