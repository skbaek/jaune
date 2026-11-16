#!/usr/bin/env python3
"""Fake `lake env CMD ...` for the incremental-capture tests: Lean's search path
is the candidate's build directory, then the fake toolchain."""
import os
import sys

assert sys.argv[1] == 'env'
os.environ['LEAN_PATH'] = os.getcwd() + '/.lake/build/lib/lean:' + os.environ['FAKE_TOOLCHAIN_LIB']
os.execvp(sys.argv[2], sys.argv[2:])
