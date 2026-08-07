"""
primeatlas -- pure-logic (no tkinter) backend package for prime_atlas_v1.py's Ustawienia
tab: configurable storage path, backup/restore (as lightweight manifests, not raw data
copies), full-database delete, and PL/EN language switching. See each module's own
docstring for details. Every class here is independently unit-testable without a
display -- settings_tab.py is the only place in this package that imports tkinter,
wiring these into actual widgets.
"""
from .app_settings import AppSettings
from .manifest import PietroSnapshot, ConstellationSnapshot, BackupManifest
from .backup_store import BackupStore
from .restore_job import RestoreJob, RestoreStep, restore_checkpoint_path
from .delete_manager import PortalWiper
from .i18n import Translator, SUPPORTED_LANGUAGES, DEFAULT_LANGUAGE, LANGUAGE_NAMES

__all__ = [
    "AppSettings",
    "PietroSnapshot", "ConstellationSnapshot", "BackupManifest",
    "BackupStore",
    "RestoreJob", "RestoreStep", "restore_checkpoint_path",
    "PortalWiper",
    "Translator", "SUPPORTED_LANGUAGES", "DEFAULT_LANGUAGE", "LANGUAGE_NAMES",
]
