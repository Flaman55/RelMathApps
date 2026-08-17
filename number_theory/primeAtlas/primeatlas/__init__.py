"""
primeatlas -- pure-logic (no tkinter) backend package for prime_atlas_v1.py's Settings
tab: configurable storage path, backup/restore (as lightweight manifests, not raw data
copies), full-database delete, and PL/EN language switching. See each module's own
docstring for details. Every class here is independently unit-testable without a
display -- settings_tab.py is the only place in this package that imports tkinter,
wiring these into actual widgets.
"""
from .app_settings import AppSettings
from .manifest import PietroSnapshot, ConstellationSnapshot, BackupManifest
from .backup_store import BackupStore
from .restore_job import (
    RestoreJob, RestoreStep, restore_checkpoint_path, prune_empty_pietro_dirs,
)
from .delete_manager import PortalWiper
from .i18n import Translator, SUPPORTED_LANGUAGES, DEFAULT_LANGUAGE, LANGUAGE_NAMES
from .primality import run_all_tests, factorize, try_import_sympy
from .goldbach_window import (
    check_window as goldbach_check_window,
    cascade_step as goldbach_cascade_step,
    next_anchor as goldbach_next_anchor,
    window_rows as goldbach_window_rows,
    largest_prime_le as goldbach_largest_prime_le,
    sieve_is_prime as goldbach_sieve_is_prime,
)

__all__ = [
    "AppSettings",
    "PietroSnapshot", "ConstellationSnapshot", "BackupManifest",
    "BackupStore",
    "RestoreJob", "RestoreStep", "restore_checkpoint_path", "prune_empty_pietro_dirs",
    "PortalWiper",
    "Translator", "SUPPORTED_LANGUAGES", "DEFAULT_LANGUAGE", "LANGUAGE_NAMES",
    "run_all_tests", "factorize", "try_import_sympy",
    "goldbach_check_window", "goldbach_cascade_step", "goldbach_next_anchor",
    "goldbach_window_rows", "goldbach_largest_prime_le", "goldbach_sieve_is_prime",
]
