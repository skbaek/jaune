"""Re-export of the validator's retired-token matcher (scripts/check-naming-map.py has a hyphen)."""
import importlib.util
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "check_naming_map", Path(__file__).resolve().parent.parent / "check-naming-map.py")
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
find_retired_tokens = _mod.find_retired_tokens
tokenize_identifier = _mod.tokenize_identifier
