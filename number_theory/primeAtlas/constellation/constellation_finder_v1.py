import sys
import os
import time
import datetime
import numpy as np

# ==========================================================================================
# constellation_finder_v1.py
#
# Scans PGS2 prime windows for k-tuple patterns ("prime constellations") defined in
# pattern_catalog_v1.py, and appends newly found matches to per-pattern hit files.
#
# Source windows are read via prime_sieve_v1.read_prime_window / read_prime_window_head
# from CONSTELLATION_PORTAL/10p{N}/source_primes/, ordered by each file's base_prime
# (from its header) rather than by an offset parsed out of the filename.
#
# Every catalog pattern (k=2 and up) is matched by the same vectorized streaming
# pipeline: each window is scanned once, together with a peek into the head of the next
# window (up to MAX_SPAN past its base_prime) so that patterns spanning a window
# boundary are still found. Because a hit's full k-tuple is always recoverable from its
# starting value plus the pattern's fixed offsets, matches only need to be stored as
# sorted starting values.
#
# Hit storage: each (k, variant) pair gets its own cumulative file,
# CONSTELLATION_PORTAL/10p{N}/constellations/k{K}/variant{ID}/HITS_10p{N}_k{K}_v{ID}.bin,
# in the same PGS2 format as source_primes windows (see prime_sieve_v1.py). New hits are
# added via prime_sieve_v1.append_prime_window() (in-place header patch + tail append,
# not a full rewrite), which keeps the cost of accumulating hits over many runs linear
# rather than quadratic in the hit file's size -- important for patterns like k=2/3/4,
# which accumulate hits fastest.
#
# Progress is tracked with a single checkpoint per floor
# (CONSTELLATION_PORTAL/10p{N}/constellations/CHECKPOINT.txt, storing the last fully-
# processed PGS2 filename), covering every k.
#
# Per-(k,variant) hit counts are available cheaply via
# read_prime_window_header(hit_path)['count'] (no full decode), which is enough to build
# an aggregate view -- e.g. for an HTML portal generator operating on
# pattern_catalog_v1.py's record_digits field -- without needing a separate report format
# maintained here.
#
# CLI: running with no floor argument auto-detects and processes every floor under the
# portal that has at least one source window (list_pietra_with_data()); an explicit
# argument restricts the run to just that one floor.
#
# Peek-ahead threshold: uses the NEXT file's header base_prime + MAX_SPAN as the peek
# threshold (via read_prime_window_head), rather than reconstructing each window's
# nominal boundary independently of its content. The two differ by at most the gap from
# a window's nominal start to its first actual prime -- a handful of units, well within
# MAX_SPAN's margin (84 at the widest catalog entry, k=21) -- so this is safe and simpler.
# ==========================================================================================

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# Self-contained alongside the rest of the app: prime_sieve_v1 lives in the sibling
# folder ../prime_sieve/.
sys.path.insert(0, os.path.join(_SCRIPT_DIR, "..", "prime_sieve"))
import prime_sieve_v1  # noqa: E402

from pattern_catalog_v1 import PATTERN_CATALOG  # noqa: E402

# CONSTELLATION_PORTAL_DIR: optional override for the portal's root folder, used by the
# GUI's Settings tab to point at a custom storage location. Falls back to a
# CONSTELLATION_PORTAL folder next to the application root (one level up from this
# file) when unset, matching AppSettings.default_storage_path.
PORTAL_FOLDER = os.environ.get("CONSTELLATION_PORTAL_DIR") or os.path.abspath(
    os.path.join(_SCRIPT_DIR, "..", "CONSTELLATION_PORTAL"))
CHECKPOINT_FILENAME = "CHECKPOINT.txt"


def list_source_windows(base_exponent):
    """Returns [(filename, path, base_prime), ...] for every PRIME_WINDOW_*.bin under
    10p{base_exponent}/source_primes/, ordered ascending by base_prime (from each file's
    header -- robust regardless of filename shorthand)."""
    source_dir = os.path.join(PORTAL_FOLDER, f"10p{base_exponent}", "source_primes")
    if not os.path.isdir(source_dir):
        return []
    entries = []
    for name in sorted(os.listdir(source_dir)):
        if not (name.startswith("PRIME_WINDOW_") and name.endswith(".bin")):
            continue
        path = os.path.join(source_dir, name)
        header = prime_sieve_v1.read_prime_window_header(path)
        entries.append((name, path, header["base_prime"]))
    entries.sort(key=lambda e: (e[2] is None, e[2] if e[2] is not None else 0, e[0]))
    return entries


def list_pietra_with_data():
    """Returns sorted base_exponent ints for every 10p{N} folder under PORTAL_FOLDER that
    actually has at least one PGS2 source window. Floor folders can exist as empty
    source_primes/constellations placeholders ahead of the scanner actually reaching
    them, so folder presence alone doesn't mean there's anything to process."""
    if not os.path.isdir(PORTAL_FOLDER):
        return []
    result = []
    for name in os.listdir(PORTAL_FOLDER):
        if name.startswith("10p") and name[3:].isdigit():
            base_exponent = int(name[3:])
            if list_source_windows(base_exponent):
                result.append(base_exponent)
    return sorted(result)


def _checkpoint_path(base_exponent):
    folder = os.path.join(PORTAL_FOLDER, f"10p{base_exponent}", "constellations")
    return os.path.join(folder, CHECKPOINT_FILENAME)


def read_checkpoint(base_exponent):
    """Returns the filename of the last fully-processed PGS2 window for this floor, or
    None if there's no checkpoint yet."""
    path = _checkpoint_path(base_exponent)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith("last_processed_file="):
                return line.split("=", 1)[1].strip()
    return None


def write_checkpoint(base_exponent, filename):
    path = _checkpoint_path(base_exponent)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"last_processed_file={filename}\n")
        f.write(f"updated_at={datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')}\n")


def hit_file_path(base_exponent, k, variant_id):
    return os.path.join(
        PORTAL_FOLDER, f"10p{base_exponent}", "constellations", f"k{k}", f"variant{variant_id}",
        f"HITS_10p{base_exponent}_k{k}_v{variant_id}.bin")


def append_hits(base_exponent, k, variant_id, new_sorted_starts, known_last_value=None):
    """Appends newly-found match starting values (already sorted, all greater than
    anything previously stored for this floor since windows are processed in increasing
    order) to this pattern's cumulative hit file -- creating the k{K}/variant{ID}/ folder
    on first use, same auto-create-what's-missing approach as the scanner uses for
    source_primes/.

    `known_last_value` is threaded straight through to append_prime_window() -- see its
    docstring. Callers making many appends to the same (k, variant) across one
    process_floor() run (the common case: k=2..5 hit files pick up new entries on almost
    every window) should track it themselves and pass it, instead of letting
    append_prime_window() re-decode the whole accumulated hit file on every single call."""
    path = hit_file_path(base_exponent, k, variant_id)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    prime_sieve_v1.append_prime_window(path, new_sorted_starts, known_last_value=known_last_value)


def match_patterns_vectorized(candidates, local_set, active_patterns):
    """Computes a presence MASK (numpy, vectorized) once per UNIQUE offset used by ANY
    tracked pattern, instead of once per (pattern, candidate, offset) triple. Matching a
    specific pattern is then a bitwise AND of its offsets' precomputed masks.

    candidates      -- Python-int list, from the CURRENT window only (each candidate is
                        used as a pattern's "base" exactly once, in its own window).
    local_set       -- Python-int set: candidates + the peeked head of the next window
                        (possible targets for p+d).
    active_patterns -- catalog entries to check (includes k=2, see file header).

    Returns {(k, id): [[p, p+d2, ..., p+dk], ...]} -- full (absolute) values.

    Computes on LOCAL offsets relative to min(candidates) -- not absolute values -- since
    numpy int64 cannot hold floor >= 19 magnitudes (see file header on why this matters
    at all only for floor >= 19; still correct and cheap either way at shallower depths).
    """
    if not candidates or not local_set:
        return {}

    base = min(candidates)
    candidates_local = np.fromiter((p - base for p in candidates), dtype=np.int64, count=len(candidates))
    local_sorted = np.fromiter(sorted(v - base for v in local_set), dtype=np.int64, count=len(local_set))

    unique_offsets = sorted(set(d for w in active_patterns for d in w["offsets"]))
    masks = {}
    for d in unique_offsets:
        shifted = candidates_local + d
        idx = np.searchsorted(local_sorted, shifted)
        idx_safe = np.clip(idx, 0, len(local_sorted) - 1)
        masks[d] = local_sorted[idx_safe] == shifted

    results = {}
    for pattern in active_patterns:
        offsets = pattern["offsets"]
        mask = masks[offsets[0]].copy()
        for d in offsets[1:]:
            mask &= masks[d]
        if not mask.any():
            continue
        key = (pattern["k"], pattern["id"])
        for i in np.nonzero(mask)[0]:
            p = candidates[int(i)]  # full-precision value from the original list
            results.setdefault(key, []).append([p + d for d in offsets])
    return results


def process_floor(base_exponent):
    """Main entry point: streams through every not-yet-processed PGS2 window for this
    floor, in order, matching every catalog pattern (k>=2) and appending new hits."""
    windows = list_source_windows(base_exponent)
    if not windows:
        print(f"[!] No source_primes windows found for 10^{base_exponent} "
              f"(expected under {PORTAL_FOLDER}/10p{base_exponent}/source_primes/).")
        return

    active_patterns = list(PATTERN_CATALOG)
    max_span = max(w["offsets"][-1] for w in active_patterns)

    last_done = read_checkpoint(base_exponent)
    names = [name for name, _, _ in windows]
    if last_done is not None and last_done in names:
        start_idx = names.index(last_done) + 1
        to_process = windows[start_idx:]
    else:
        if last_done is not None:
            print(f"[!] Checkpointed file {last_done!r} not found among current windows "
                  f"-- ignoring checkpoint, processing from the start.")
        to_process = windows

    print(f"\n[CONSTELLATIONS v1] 10^{base_exponent}: {len(to_process)}/{len(windows)} "
          f"windows to process | patterns active: {len(active_patterns)} (k>=2) | "
          f"MAX_SPAN={max_span}")

    if not to_process:
        print("[CONSTELLATIONS v1] Nothing new -- checkpoint is up to date.")
        return

    total_hits_this_run = {}
    # (k, variant_id) -> last stored value in that pattern's cumulative hit file, tracked
    # IN MEMORY across this whole run so append_hits() never has to re-decode the
    # already-accumulated hit file just to find where to resume gap-encoding from.
    # Without this, every append re-read the WHOLE growing file (see
    # append_prime_window()'s docstring in prime_sieve_v1.py) -- for common patterns like
    # k=2..5, which pick up new hits on nearly every window, that makes the total append
    # cost quadratic in the hit file's size over a floor's lifetime. Bootstrapped lazily
    # (at most once per pattern per run, from disk) the first time a pattern actually gets
    # a hit in this run.
    last_value_cache = {}

    for i, (name, path, _base_prime) in enumerate(to_process):
        t0 = time.time()
        candidates = prime_sieve_v1.read_prime_window(path)

        head = []
        if i + 1 < len(to_process):
            next_name, next_path, next_base = to_process[i + 1]
            if next_base is not None:
                head = prime_sieve_v1.read_prime_window_head(next_path, next_base + max_span)

        local_set = set(candidates)
        local_set.update(head)

        results = match_patterns_vectorized(candidates, local_set, active_patterns)
        new_hits_count = 0
        for (k, vid), matches in results.items():
            starts = sorted(m[0] for m in matches)
            key = (k, vid)
            if key not in last_value_cache:
                hpath = hit_file_path(base_exponent, k, vid)
                if os.path.exists(hpath):
                    existing = prime_sieve_v1.read_prime_window(hpath)
                    last_value_cache[key] = existing[-1] if existing else None
                else:
                    last_value_cache[key] = None
            append_hits(base_exponent, k, vid, starts, known_last_value=last_value_cache[key])
            last_value_cache[key] = starts[-1]
            total_hits_this_run[key] = total_hits_this_run.get(key, 0) + len(starts)
            new_hits_count += len(starts)

        write_checkpoint(base_exponent, name)

        print(f"[CONSTELLATIONS v1] {i+1}/{len(to_process)}: {name} -- "
              f"primes={len(candidates):,} peeked_head={len(head)} "
              f"new_hits={new_hits_count} ({time.time()-t0:.2f}s)")

    print(f"\n[CONSTELLATIONS v1] Done. New hits this run, by pattern:")
    if not total_hits_this_run:
        print("    (none)")
    for (k, vid), count in sorted(total_hits_this_run.items()):
        print(f"    k={k:2} variant={vid}: +{count}")


if __name__ == "__main__":
    print("=" * 70)
    print("[*] CONSTELLATION FINDER -- v1 (PGS2 streaming + unified k=2..21 + "
          "in-place-append hit files)")
    print("=" * 70)

    print(f"[*] Portal: {PORTAL_FOLDER}")
    print("Start time:", datetime.datetime.now().strftime("%H:%M:%S"))

    if len(sys.argv) > 1:
        floors = [int(sys.argv[1])]
    else:
        # No floor given -- auto-detect every one that actually has source_primes data.
        # process_floor() is already a cheap no-op for a floor whose checkpoint is fully
        # caught up, so scanning all of them each run is safe, not just at the moment a
        # new floor's data first appears.
        floors = list_pietra_with_data()
        if not floors:
            print("[!] No floor folders with source_primes data found under the portal -- nothing to do.")
        else:
            print(f"[*] No floor given on the command line -- auto-detected {len(floors)} "
                  f"with data: {', '.join('10^' + str(n) for n in floors)}")

    for base_exponent in floors:
        process_floor(base_exponent)
