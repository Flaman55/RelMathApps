"""
delete_manager.py -- PortalWiper, deletes an ENTIRE portal storage location: every
10p{N} floor folder (source windows + constellations), and truncates benchmark_log.csv
back to just its header. Deliberately does NOT touch _backups/ -- backups are the whole
point of offering this button safely at all.

The warning/confirmation dialog itself lives in settings_tab.py (needs tkinter); this
module is the pure logic behind it -- plan() for what the dialog should show, execute()
for what OK actually does. A destructive full-wipe action is only offered behind an
explicit warning and a recommendation to back up first.
"""
import os
import shutil
import re
import csv

_PIETRO_DIR_RE = re.compile(r"^10p(\d+)$")


class PortalWiper:
    def __init__(self, storage_path):
        self.storage_path = storage_path

    def plan(self):
        """Dry-run: what WOULD be deleted, for the confirmation dialog. Returns
        (pietro_names, benchmark_row_count) without touching anything on disk."""
        pietra = []
        if os.path.isdir(self.storage_path):
            for name in os.listdir(self.storage_path):
                if _PIETRO_DIR_RE.match(name) and os.path.isdir(os.path.join(self.storage_path, name)):
                    pietra.append(name)
        pietra.sort()
        csv_path = os.path.join(self.storage_path, "benchmark_log.csv")
        row_count = 0
        if os.path.exists(csv_path):
            try:
                with open(csv_path, newline="", encoding="utf-8") as f:
                    row_count = sum(1 for _ in csv.DictReader(f))
            except OSError:
                row_count = 0
        return pietra, row_count

    def execute(self):
        """Actually deletes. Returns (deleted_pietra, errors) -- best-effort: a single
        locked/undeletable file shouldn't abort the whole wipe, it just gets reported so
        the caller can show the user what didn't go through."""
        pietra, _ = self.plan()
        deleted = []
        errors = []
        for name in pietra:
            path = os.path.join(self.storage_path, name)
            try:
                shutil.rmtree(path)
                deleted.append(name)
            except OSError as e:
                errors.append(f"{name}: {e}")

        csv_path = os.path.join(self.storage_path, "benchmark_log.csv")
        if os.path.exists(csv_path):
            try:
                with open(csv_path, newline="", encoding="utf-8") as f:
                    header = next(csv.reader(f), None)
                if header is not None:
                    tmp_path = f"{csv_path}.tmp{os.getpid()}"
                    with open(tmp_path, "w", newline="", encoding="utf-8") as f:
                        csv.writer(f).writerow(header)
                    os.replace(tmp_path, csv_path)
            except OSError as e:
                errors.append(f"benchmark_log.csv: {e}")

        return deleted, errors
