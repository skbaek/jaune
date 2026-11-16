#!/usr/bin/env python3
"""Fake owned build: `jaune-naming-fidelity` installs the fake exporter (its
bytes carry FAKE_EXPORTER_VARIANT); a module target writes an `.olean` and
`.ir` whose bytes are the module's source digest."""
import hashlib
import os
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
for target in sys.argv[1:]:
    if target == 'jaune-naming-fidelity':
        exe = Path('.lake/build/bin/jaune-naming-fidelity')
        exe.parent.mkdir(parents=True, exist_ok=True)
        exe.write_text((here / 'fake_exporter.py').read_text() +
                       f"\n# variant {os.environ.get('FAKE_EXPORTER_VARIANT', '0')}\n")
        exe.chmod(0o755)
        continue
    digest = hashlib.sha256(Path(target.replace('.', '/') + '.lean').read_bytes()).hexdigest()
    olean = Path('.lake/build/lib/lean') / (target.replace('.', '/') + '.olean')
    olean.parent.mkdir(parents=True, exist_ok=True)
    olean.write_text(digest)
    olean.with_suffix('.ir').write_text('ir ' + digest)
