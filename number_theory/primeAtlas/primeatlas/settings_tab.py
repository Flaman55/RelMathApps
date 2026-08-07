"""
settings_tab.py -- SettingsTab, the tkinter widgets for the Ustawienia tab: language
switch, storage-path configuration, backup create/list, restore (diff-against-disk ->
confirm -> checkpointed, pausable/resumable/cancellable regeneration job), and the
full-database delete button.

This is the ONLY file in primeatlas/ that imports tkinter -- every other module in this
package is pure logic, unit-tested without a display (see __init__.py's docstring).
SettingsTab is built and imported lazily, exactly once, from inside prime_atlas_v1.py's
_build_gui() (itself deferred past module-import time for the same reason -- see that
function's own docstring) -- so by the time this module is imported, tkinter is already
known to be importable; no further lazy-import gymnastics are needed here.

SettingsTab does NOT know how to launch orchestrator_loop_v2.py / constellation_finder_v1.py
itself -- prime_atlas_v1.py already owns that machinery (build_loop_argv,
build_constellation_finder_argv, build_wsl_logged_command, WslLoggedRunner,
generation_log_paths -- built for the Generowanie tab) and hands it to this class as a
small dict of callables (`wsl_helpers`) at construction time instead of this module
re-implementing a second copy or importing prime_atlas_v1.py directly (which would be
circular: that file imports SettingsTab from this package). Expected keys:
  - get_portal_folder() -> str                     current storage path, read at call time
  - set_portal_folder(path) -> None                 rebinds the app's global + status label
  - get_loop_defaults() -> dict                     current Generowanie-tab loop form values
  - build_loop_argv, build_constellation_finder_argv, build_wsl_logged_command  (functions)
  - WslLoggedRunner                                  (class)
  - generation_log_paths                             (function)

Restore driving semantics: orchestrator_loop_v2.py doesn't accept "regenerate exactly these
offsets" -- it appends the next N windows from wherever a piętro's file count currently sits.
Since prime_sieve_v1.py assigns offsets deterministically in a fixed sequence per piętro,
restarting generation on a piętro with fewer files than the backup recorded reproduces the
SAME missing filenames in the SAME order -- so "run enough iterations to cover the missing
count, then re-diff" is a correct (if occasionally slightly wasteful on the last window)
restore strategy, not an approximation. Each step retries a bounded number of times
(MAX_STAGE_RETRIES) before being marked done anyway with a logged warning -- consistent with
this project's existing best-effort philosophy (see delete_manager.py's PortalWiper.execute()
docstring).

Every user-visible string in this file goes through self.T(key, **kwargs) -- a
Translator instance (primeatlas/i18n.py) passed in at construction, backed by
locales/strings_pl.json and locales/strings_en.json. The language PICKER lives in this
tab (top of _build_widgets) but only writes the choice to AppSettings -- it does NOT
rebuild this tab's own already-built widgets, since a live-relabel of every widget in
all 5 tabs would be a much larger and riskier change than a restart-required switch
(see i18n.py's own docstring for the full rationale). The Ustawienia tab shows a note
saying the change takes effect after restarting the app.
"""
import os
import queue

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tkinter.scrolledtext import ScrolledText

from .manifest import PietroSnapshot, ConstellationSnapshot
from .backup_store import BackupStore
from .restore_job import (
    RestoreJob, restore_checkpoint_path, delete_extra_files,
    STATUS_RUNNING, STATUS_PAUSED,
)
from .delete_manager import PortalWiper
from .i18n import Translator, SUPPORTED_LANGUAGES


class SettingsTab(ttk.Frame):
    MAX_STAGE_RETRIES = 2

    def __init__(self, parent, app_settings, wsl_helpers, translator):
        super().__init__(parent)
        self.app_settings = app_settings
        self.wsl = wsl_helpers
        self.T = translator

        self._backups = []              # [(name, path)], newest first
        self._selected_backup_name = None
        self._diff_cache = None         # last "check differences" result for the selection

        self._active_job = None         # RestoreJob currently driving, or None
        self._active_job_runner_kind = None  # "loop" / "constellation" / None (in flight)
        self._restore_runner = None
        self._restore_queue = None
        self._step_retry_counts = {}
        self._incomplete_jobs = []

        self._build_widgets()
        self._refresh_backup_list()
        self._scan_incomplete_restores()

    # ---- language -----------------------------------------------------------------------

    def _on_language_selected(self, _event=None):
        label = self.language_var.get()
        code = self._language_codes_by_label.get(label)
        if code is None or code == self.app_settings.language:
            return
        self.app_settings.set_language(code)
        # The person changing language usually can't read the CURRENT one (that's why
        # they're switching) -- so this confirmation has to speak the NEWLY chosen
        # language, not self.T (still bound to the language the app was launched with,
        # since the switch itself is restart-required). A throwaway Translator for just
        # this one popup is cheap and doesn't touch self.T or rebuild any other widget.
        target_t = Translator(code).t
        messagebox.showinfo(target_t("settings.dialog_title"),
                             target_t("settings.language_restart_note"))

    # ---- storage path -----------------------------------------------------------------

    def _path_status_text(self):
        return (self.T("settings.path_custom") if self.app_settings.is_custom
                else self.T("settings.path_default"))

    def _on_browse_path(self):
        chosen = filedialog.askdirectory(
            initialdir=self.path_var.get() or self.app_settings.default_storage_path,
            title=self.T("settings.path_browse_title"))
        if chosen:
            self.path_var.set(chosen)

    def _on_save_path(self):
        new_path = self.path_var.get().strip()
        if not new_path:
            messagebox.showerror(self.T("settings.dialog_title"),
                                  self.T("settings.path_empty_msg"))
            return
        self.app_settings.set_storage_path(new_path)
        self.wsl["set_portal_folder"](self.app_settings.storage_path)
        self.path_var.set(self.app_settings.storage_path)
        self.path_status_var.set(self._path_status_text())
        self._refresh_backup_list()
        self._scan_incomplete_restores()
        messagebox.showinfo(self.T("settings.dialog_title"),
                             self.T("settings.path_saved_msg", path=self.app_settings.storage_path))

    def _on_reset_path(self):
        self.app_settings.set_storage_path(None)
        self.wsl["set_portal_folder"](self.app_settings.storage_path)
        self.path_var.set(self.app_settings.storage_path)
        self.path_status_var.set(self._path_status_text())
        self._refresh_backup_list()
        self._scan_incomplete_restores()

    # ---- backup -------------------------------------------------------------------------

    def _current_backup_store(self):
        # Rebuilt on every call (not cached) so it always reflects whatever storage path
        # is CURRENT -- the user can change the path without recreating this tab.
        return BackupStore(self.wsl["get_portal_folder"]())

    def _on_create_backup(self):
        store = self._current_backup_store()
        manifest = store.create()
        self.backup_status_var.set(self.T("settings.backup_created", name=manifest.name))
        self._refresh_backup_list()

    def _refresh_backup_list(self):
        store = self._current_backup_store()
        self._backups = store.list_backups()
        self.backup_listbox.delete(0, "end")
        for name, _path in self._backups:
            self.backup_listbox.insert("end", name)
        self._selected_backup_name = None
        self._diff_cache = None
        self.restore_start_btn.configure(state="disabled")

    def _on_backup_selected(self, _event):
        sel = self.backup_listbox.curselection()
        if not sel:
            return
        self._selected_backup_name = self.backup_listbox.get(sel[0])
        self._diff_cache = None
        self.restore_start_btn.configure(state="disabled")

    # ---- restore: diff + start ----------------------------------------------------------

    def _on_check_diff(self):
        if not self._selected_backup_name:
            messagebox.showinfo(self.T("settings.restore_title"),
                                 self.T("settings.restore_select_backup_first"))
            return
        if self._active_job is not None and self._active_job.status == STATUS_RUNNING:
            messagebox.showinfo(self.T("settings.restore_title"),
                                 self.T("settings.restore_already_running"))
            return
        store = self._current_backup_store()
        manifest = store.load(self._selected_backup_name)
        portal_folder = self.wsl["get_portal_folder"]()
        diff = manifest.diff_against_disk(portal_folder)
        self._diff_cache = diff
        if not diff:
            self._restore_log(
                self.T("settings.restore_no_diff", name=self._selected_backup_name))
            self.restore_start_btn.configure(state="disabled")
            return
        lines = [self.T("settings.restore_diff_header", name=self._selected_backup_name)]
        for base_exponent, d in sorted(diff.items()):
            lines.append(self.T(
                "settings.restore_diff_line", base_exponent=base_exponent,
                windows=len(d["missing_windows"]), hits=len(d["missing_hits"]),
                extra_windows=len(d.get("extra_windows", [])),
                extra_hits=len(d.get("extra_hits", []))))
        self._restore_log("".join(lines))
        self.restore_start_btn.configure(state="normal")

    def _on_start_restore(self):
        if not self._selected_backup_name or self._diff_cache is None:
            return
        # Gdy magazyn ma więcej niż backup (np. nowe piętro dodane po zrobieniu backupu),
        # restore do tego backupu usunie nadmiar -- to jest destrukcyjne, więc osobne,
        # jawne ostrzeżenie PRZED ogólnym potwierdzeniem restore, z możliwością
        # anulowania w tym miejscu.
        extra_pietra = {
            be: d for be, d in self._diff_cache.items()
            if d.get("extra_windows") or d.get("extra_hits")
        }
        if extra_pietra:
            extra_lines = "".join(
                self.T("settings.restore_extra_line", base_exponent=be,
                        windows=len(d.get("extra_windows", [])),
                        hits=len(d.get("extra_hits", [])))
                for be, d in sorted(extra_pietra.items()))
            if not messagebox.askyesno(
                    self.T("settings.restore_title"),
                    self.T("settings.restore_confirm_delete_extra",
                           name=self._selected_backup_name, lines=extra_lines)):
                return
        if not messagebox.askyesno(
                self.T("settings.restore_title"),
                self.T("settings.restore_confirm", name=self._selected_backup_name)):
            return
        # Restore also swaps in the backup's benchmark_log.csv: its row history for
        # windows/piętra that never made it into the backup (e.g. a piętro added after
        # the backup was taken) has to go away along with their files, and rows for
        # anything regenerated below get freshly re-appended by that generation run
        # anyway (same WSL pipeline that writes benchmark_log.csv during ordinary
        # generation -- see orchestrator_loop_v2.py/prime_sieve_v3.py).
        # BackupStore.restore_csv() does the full swap-in of the backup's own CSV
        # snapshot; it's called here, once, at the START of a NEW job -- not from
        # _on_resume_incomplete(), which continues a job whose CSV was already restored
        # when it was first started.
        store = self._current_backup_store()
        manifest = store.load(self._selected_backup_name)
        store.restore_csv(manifest)
        self._restore_log(self.T("settings.restore_csv_restored", name=self._selected_backup_name))
        portal_folder = self.wsl["get_portal_folder"]()
        checkpoint_path = restore_checkpoint_path(portal_folder, self._selected_backup_name)
        job = RestoreJob.from_diff(self._selected_backup_name, self._diff_cache, checkpoint_path)
        job.start()
        self._active_job = job
        self._step_retry_counts = {}
        self._update_restore_progress()
        self._update_restore_buttons()
        self._drive_restore()

    def _on_resume_incomplete(self):
        sel = self.incomplete_listbox.curselection()
        if not sel or not self._incomplete_jobs:
            return
        job = self._incomplete_jobs[sel[0]]
        if job.status == STATUS_RUNNING:
            # App restarted (or crashed) while this job was running -- no subprocess is
            # actually alive anymore, so treat it as PAUSED until the user explicitly
            # clicks Resume, rather than silently resuming into a false "already running".
            job.status = STATUS_PAUSED
            job.save()
        self._active_job = job
        self._step_retry_counts = {}
        self._restore_log(self.T("settings.restore_loaded_incomplete", name=job.backup_name))
        self._update_restore_progress()
        self._update_restore_buttons()

    # ---- restore: pause/resume/cancel ----------------------------------------------------

    def _on_restore_pause(self):
        if self._active_job:
            self._active_job.pause()
            self._restore_log(self.T("settings.restore_paused_note"))
            self._update_restore_buttons()

    def _on_restore_resume(self):
        if self._active_job:
            self._active_job.resume()
            self._restore_log(self.T("settings.restore_resumed_note"))
            self._update_restore_buttons()
            self._drive_restore()

    def _on_restore_cancel(self):
        if self._active_job is None:
            return
        if not messagebox.askyesno(self.T("settings.restore_title"),
                                    self.T("settings.restore_confirm_cancel")):
            return
        if self._restore_runner is not None:
            self._restore_runner.stop()
        self._active_job.cancel()
        self._restore_log(self.T("settings.restore_cancelled_note"))
        self._update_restore_buttons()

    # ---- restore: driver (one piętro/step at a time) -------------------------------------

    def _drive_restore(self):
        """Kicks off the next unit of restore work. No-op if there is no active job, the job
        isn't RUNNING (paused/cancelled/completed), or a subprocess is already in flight for
        it (that subprocess's own completion callback calls back into this method)."""
        job = self._active_job
        if job is None or job.status != STATUS_RUNNING:
            return
        if self._active_job_runner_kind is not None:
            return
        step = job.next_step()
        if step is None:
            self._on_restore_job_finished()
            return
        self._restore_log(self.T(
            "settings.restore_step_start", base_exponent=step.base_exponent,
            windows=len(step.missing_windows), hits=len(step.missing_hits)))
        if step.needs_windows:
            self._start_loop_for_step(step)
        elif step.needs_hits:
            self._start_constellation_for_step(step)
        else:
            self._finish_step(step)

    def _finish_step(self, step):
        """Called once a step has nothing left that needs REGENERATING (no missing windows
        or hits, possibly after giving up per MAX_STAGE_RETRIES). If the step also has
        surplus files on disk that aren't in the backup, delete them now -- this is a pure
        local file op (delete_extra_files(), no WSL subprocess), so it runs synchronously
        right here rather than through the poll/subprocess machinery. The confirm/cancel
        warning already happened once, up front in _on_start_restore(), before the whole
        job was ever started."""
        job = self._active_job
        if step.has_extra:
            portal_folder = self.wsl["get_portal_folder"]()
            deleted, pruned, errors = delete_extra_files(
                portal_folder, step.base_exponent, step.extra_windows, step.extra_hits)
            self._restore_log(self.T(
                "settings.restore_extra_deleted", base_exponent=step.base_exponent,
                deleted=deleted))
            if pruned:
                self._restore_log(self.T(
                    "settings.restore_extra_pruned", base_exponent=step.base_exponent,
                    pruned=pruned))
            if errors:
                self._restore_log(self.T("settings.restore_extra_delete_errors"))
                for e in errors:
                    self._restore_log(f"  {e}\n")
            step.extra_windows = []
            step.extra_hits = []
        job.mark_step_done(step.base_exponent)
        self._update_restore_progress()
        self._drive_restore()

    def _start_loop_for_step(self, step):
        self._active_job_runner_kind = "loop"
        defaults = self.wsl["get_loop_defaults"]()
        window_count_per_run = int(defaults.get("window_count_per_run") or 20)
        n_instances = int(defaults.get("n_instances") or 1)
        workers = int(defaults.get("workers") or 1)
        batches_per_worker = int(defaults.get("batches_per_worker") or 1)
        compute_sieving = bool(defaults.get("compute_sieving_primes_count", False))
        window_m = int(defaults.get("window_m") or 10_000_000)
        run_count = max(1, -(-len(step.missing_windows) // max(1, window_count_per_run)))
        argv = self.wsl["build_loop_argv"](
            step.base_exponent, run_count, n_instances, True, compute_sieving,
            window_count_per_run, workers, batches_per_worker, window_m)
        portal_folder = self.wsl["get_portal_folder"]()
        log_path, exit_path, _run_id = self.wsl["generation_log_paths"](
            portal_folder, "restore_loop")
        cmd = self.wsl["build_wsl_logged_command"](argv, log_path, exit_path)
        q = queue.Queue()
        runner = self.wsl["WslLoggedRunner"](
            cmd, log_path, exit_path, q, kill_pattern="orchestrator_loop_v2.py")
        self._restore_runner = runner
        self._restore_queue = q
        runner.start()
        self._poll_restore_queue(step, "loop")

    def _start_constellation_for_step(self, step):
        self._active_job_runner_kind = "constellation"
        argv = self.wsl["build_constellation_finder_argv"](step.base_exponent)
        portal_folder = self.wsl["get_portal_folder"]()
        log_path, exit_path, _run_id = self.wsl["generation_log_paths"](
            portal_folder, "restore_const")
        cmd = self.wsl["build_wsl_logged_command"](argv, log_path, exit_path)
        q = queue.Queue()
        runner = self.wsl["WslLoggedRunner"](
            cmd, log_path, exit_path, q, kill_pattern="constellation_finder_v1.py")
        self._restore_runner = runner
        self._restore_queue = q
        runner.start()
        self._poll_restore_queue(step, "constellation")

    def _poll_restore_queue(self, step, kind):
        try:
            while True:
                item = self._restore_queue.get_nowait()
                if isinstance(item, tuple) and item and item[0] == "__exit__":
                    self._restore_log(self.T("settings.restore_stage_done", kind=kind, code=item[1]))
                    self._on_step_stage_done(step, kind)
                    return
                self._restore_log(item)
        except queue.Empty:
            pass
        self.after(150, lambda: self._poll_restore_queue(step, kind))

    def _on_step_stage_done(self, step, kind):
        job = self._active_job
        self._active_job_runner_kind = None
        self._restore_runner = None
        if job is None:
            return
        portal_folder = self.wsl["get_portal_folder"]()
        if kind == "loop":
            current = PietroSnapshot.scan(portal_folder, step.base_exponent)
            step.missing_windows = sorted(set(step.missing_windows) - set(current.filenames))
        else:
            current_c = ConstellationSnapshot.scan(portal_folder, step.base_exponent)
            step.missing_hits = sorted(set(step.missing_hits) - set(current_c.hit_files))
        job.save()

        if job.status != STATUS_RUNNING:
            return  # paused/cancelled while the subprocess was running -- don't auto-continue

        retries = self._step_retry_counts.get(step.base_exponent, 0)
        if step.needs_windows and retries < self.MAX_STAGE_RETRIES:
            self._step_retry_counts[step.base_exponent] = retries + 1
            self._restore_log(self.T(
                "settings.restore_retry_windows", base_exponent=step.base_exponent,
                count=len(step.missing_windows)))
            self._start_loop_for_step(step)
            return
        if step.needs_hits and retries < self.MAX_STAGE_RETRIES:
            self._step_retry_counts[step.base_exponent] = retries + 1
            self._start_constellation_for_step(step)
            return
        if step.needs_windows or step.needs_hits:
            self._restore_log(self.T(
                "settings.restore_gave_up", base_exponent=step.base_exponent,
                windows=len(step.missing_windows), hits=len(step.missing_hits)))
        else:
            self._restore_log(self.T("settings.restore_step_done", base_exponent=step.base_exponent))
        self._finish_step(step)

    def _on_restore_job_finished(self):
        self._restore_log(self.T("settings.restore_job_finished", name=self._active_job.backup_name))
        self._active_job = None
        self._update_restore_progress()
        self._update_restore_buttons()
        self._scan_incomplete_restores()

    def _scan_incomplete_restores(self):
        portal_folder = self.wsl["get_portal_folder"]()
        backups_dir = os.path.join(portal_folder, "_backups")
        found = []
        if os.path.isdir(backups_dir):
            for fname in sorted(os.listdir(backups_dir)):
                if not fname.endswith(".restore.json"):
                    continue
                path = os.path.join(backups_dir, fname)
                try:
                    job = RestoreJob.load(path)
                except (OSError, ValueError, KeyError):
                    continue
                if job is not None and job.pending_steps:
                    found.append(job)
        self._incomplete_jobs = found
        self.incomplete_listbox.delete(0, "end")
        for job in found:
            done, total = job.progress
            self.incomplete_listbox.insert(
                "end", f"{job.backup_name}  [{job.status}]  {done}/{total}")

    # ---- restore: progress/log widgets ---------------------------------------------------

    def _update_restore_buttons(self):
        job = self._active_job
        running_now = job is not None and job.status == STATUS_RUNNING
        paused = job is not None and job.status == STATUS_PAUSED
        self.restore_pause_btn.configure(state="normal" if running_now else "disabled")
        self.restore_resume_btn.configure(state="normal" if paused else "disabled")
        self.restore_cancel_btn.configure(
            state="normal" if (running_now or paused) else "disabled")

    def _update_restore_progress(self):
        job = self._active_job
        if job is None:
            self.restore_progress.configure(maximum=1, value=0)
            self.restore_progress_label.set("")
            return
        done, total = job.progress
        self.restore_progress.configure(maximum=max(1, total), value=done)
        self.restore_progress_label.set(self.T(
            "settings.restore_progress_label", name=job.backup_name, done=done, total=total,
            status=job.status))

    def _restore_log(self, text):
        self.restore_output.configure(state="normal")
        self.restore_output.insert("end", text)
        self.restore_output.see("end")
        self.restore_output.configure(state="disabled")

    # ---- delete ---------------------------------------------------------------------------

    def _on_delete_clicked(self):
        portal_folder = self.wsl["get_portal_folder"]()
        wiper = PortalWiper(portal_folder)
        pietra, row_count = wiper.plan()
        if not pietra and row_count == 0:
            messagebox.showinfo(self.T("settings.delete_title"),
                                 self.T("settings.delete_already_empty"))
            return

        dialog = tk.Toplevel(self)
        dialog.title(self.T("settings.delete_dialog_title"))
        dialog.transient(self.winfo_toplevel())
        dialog.grab_set()

        msg = self.T(
            "settings.delete_confirm_msg",
            count=len(pietra), names=(", ".join(pietra) if pietra else "-"),
            rows=row_count, folder=portal_folder)
        ttk.Label(dialog, text=msg, wraplength=480, justify="left").pack(padx=16, pady=16)

        btn_row = ttk.Frame(dialog)
        btn_row.pack(pady=(0, 16))

        def do_backup_and_delete():
            store = self._current_backup_store()
            manifest = store.create()
            self._refresh_backup_list()
            deleted, errors = wiper.execute()
            dialog.destroy()
            self._report_delete_result(deleted, errors, backed_up_as=manifest.name)

        def do_delete_only():
            deleted, errors = wiper.execute()
            dialog.destroy()
            self._report_delete_result(deleted, errors, backed_up_as=None)

        def do_cancel():
            dialog.destroy()

        ttk.Button(btn_row, text=self.T("settings.delete_backup_and_delete"),
                   command=do_backup_and_delete).pack(side="left", padx=6)
        ttk.Button(btn_row, text=self.T("settings.delete_only"),
                   command=do_delete_only).pack(side="left", padx=6)
        ttk.Button(btn_row, text=self.T("settings.delete_cancel"),
                   command=do_cancel).pack(side="left", padx=6)

    def _report_delete_result(self, deleted, errors, backed_up_as):
        lines = []
        if backed_up_as:
            lines.append(self.T("settings.delete_backed_up_as", name=backed_up_as))
        lines.append(self.T(
            "settings.delete_result", count=len(deleted),
            names=(", ".join(deleted) if deleted else "-")))
        if errors:
            lines.append(self.T("settings.delete_errors_header"))
            lines.extend(f"  {e}" for e in errors)
        text = "\n".join(lines)
        self._restore_log(text + "\n")
        if errors:
            messagebox.showwarning(self.T("settings.delete_title"), text)
        else:
            messagebox.showinfo(self.T("settings.delete_title"), text)
        self._refresh_backup_list()
        self._scan_incomplete_restores()

    # ---- widget construction ---------------------------------------------------------------

    def _build_widgets(self):
        outer = ttk.Frame(self)
        outer.pack(fill="both", expand=True, padx=6, pady=6)

        lang_frame = ttk.Labelframe(outer, text=self.T("settings.language_frame"))
        lang_frame.pack(fill="x", pady=(0, 8))
        ttk.Label(lang_frame, text=self.T("settings.language_label")).grid(
            row=0, column=0, sticky="w", padx=6, pady=6)
        available = Translator.available_languages()
        self._language_codes_by_label = {label: code for code, label in available}
        self._language_labels_by_code = {code: label for code, label in available}
        current_label = self._language_labels_by_code.get(
            self.app_settings.language, self.app_settings.language)
        self.language_var = tk.StringVar(value=current_label)
        language_combo = ttk.Combobox(
            lang_frame, textvariable=self.language_var, state="readonly",
            values=[label for _code, label in available], width=20)
        language_combo.grid(row=0, column=1, sticky="w", padx=(0, 12), pady=6)
        language_combo.bind("<<ComboboxSelected>>", self._on_language_selected)
        ttk.Label(lang_frame, text=self.T("settings.language_restart_note"),
                  foreground="#555555").grid(row=0, column=2, sticky="w", padx=(0, 6), pady=6)

        path_frame = ttk.Labelframe(outer, text=self.T("settings.path_frame"))
        path_frame.pack(fill="x", pady=(0, 8))
        self.path_var = tk.StringVar(value=self.wsl["get_portal_folder"]())
        ttk.Entry(path_frame, textvariable=self.path_var, width=70).grid(
            row=0, column=0, sticky="we", padx=6, pady=6)
        path_frame.columnconfigure(0, weight=1)
        ttk.Button(path_frame, text=self.T("settings.path_browse"),
                   command=self._on_browse_path).grid(row=0, column=1, padx=4)
        ttk.Button(path_frame, text=self.T("settings.path_save"),
                   command=self._on_save_path).grid(row=0, column=2, padx=4)
        ttk.Button(path_frame, text=self.T("settings.path_reset"),
                   command=self._on_reset_path).grid(row=0, column=3, padx=(4, 6))
        self.path_status_var = tk.StringVar(value=self._path_status_text())
        ttk.Label(path_frame, textvariable=self.path_status_var, foreground="#555555").grid(
            row=1, column=0, columnspan=4, sticky="w", padx=6, pady=(0, 6))

        backup_frame = ttk.Labelframe(outer, text=self.T("settings.backup_frame"))
        backup_frame.pack(fill="x", pady=(0, 8))
        btn_row = ttk.Frame(backup_frame)
        btn_row.pack(fill="x", padx=6, pady=(6, 2))
        ttk.Button(btn_row, text=self.T("settings.backup_create"),
                   command=self._on_create_backup).pack(side="left")
        ttk.Button(btn_row, text=self.T("settings.backup_refresh"),
                   command=self._refresh_backup_list).pack(side="left", padx=(6, 0))
        self.backup_status_var = tk.StringVar(value="")
        ttk.Label(btn_row, textvariable=self.backup_status_var).pack(side="left", padx=(12, 0))

        list_row = ttk.Frame(backup_frame)
        list_row.pack(fill="x", padx=6, pady=(0, 6))
        self.backup_listbox = tk.Listbox(list_row, height=5, exportselection=False)
        self.backup_listbox.pack(side="left", fill="x", expand=True)
        self.backup_listbox.bind("<<ListboxSelect>>", self._on_backup_selected)
        scrollbar = ttk.Scrollbar(list_row, orient="vertical", command=self.backup_listbox.yview)
        scrollbar.pack(side="left", fill="y")
        self.backup_listbox.configure(yscrollcommand=scrollbar.set)

        restore_frame = ttk.Labelframe(outer, text=self.T("settings.restore_frame"))
        restore_frame.pack(fill="both", expand=True, pady=(0, 8))

        restore_btn_row = ttk.Frame(restore_frame)
        restore_btn_row.pack(fill="x", padx=6, pady=(6, 2))
        self.restore_diff_btn = ttk.Button(
            restore_btn_row, text=self.T("settings.restore_check_diff"), command=self._on_check_diff)
        self.restore_diff_btn.pack(side="left")
        self.restore_start_btn = ttk.Button(
            restore_btn_row, text=self.T("settings.restore_start"), command=self._on_start_restore,
            state="disabled")
        self.restore_start_btn.pack(side="left", padx=(6, 0))
        self.restore_pause_btn = ttk.Button(
            restore_btn_row, text=self.T("settings.restore_pause"), command=self._on_restore_pause,
            state="disabled")
        self.restore_pause_btn.pack(side="left", padx=(6, 0))
        self.restore_resume_btn = ttk.Button(
            restore_btn_row, text=self.T("settings.restore_resume"), command=self._on_restore_resume,
            state="disabled")
        self.restore_resume_btn.pack(side="left", padx=(6, 0))
        self.restore_cancel_btn = ttk.Button(
            restore_btn_row, text=self.T("settings.restore_cancel"), command=self._on_restore_cancel,
            state="disabled")
        self.restore_cancel_btn.pack(side="left", padx=(6, 0))

        self.restore_progress = ttk.Progressbar(
            restore_frame, orient="horizontal", mode="determinate", maximum=1, value=0)
        self.restore_progress.pack(fill="x", padx=6, pady=(2, 2))
        self.restore_progress_label = tk.StringVar(value="")
        ttk.Label(restore_frame, textvariable=self.restore_progress_label).pack(
            anchor="w", padx=6)

        incomplete_row = ttk.Frame(restore_frame)
        incomplete_row.pack(fill="x", padx=6, pady=(4, 2))
        ttk.Label(incomplete_row, text=self.T("settings.restore_incomplete_label")).pack(anchor="w")
        self.incomplete_listbox = tk.Listbox(incomplete_row, height=3, exportselection=False)
        self.incomplete_listbox.pack(fill="x", side="left", expand=True)
        ttk.Button(incomplete_row, text=self.T("settings.restore_resume_selected"),
                   command=self._on_resume_incomplete).pack(side="left", padx=(6, 0))

        self.restore_output = ScrolledText(
            restore_frame, height=8, font=("Consolas", 9), state="disabled",
            background="#111318", foreground="#d8d8d8")
        self.restore_output.pack(fill="both", expand=True, padx=6, pady=(4, 6))

        delete_frame = ttk.Labelframe(outer, text=self.T("settings.delete_frame"))
        delete_frame.pack(fill="x")
        ttk.Label(
            delete_frame, text=self.T("settings.delete_warning"),
            foreground="#a33", wraplength=760, justify="left").pack(
            anchor="w", padx=6, pady=(6, 4))
        ttk.Button(delete_frame, text=self.T("settings.delete_button"),
                   command=self._on_delete_clicked).pack(anchor="w", padx=6, pady=(0, 6))
