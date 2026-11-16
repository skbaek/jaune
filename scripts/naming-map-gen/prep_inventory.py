#!/usr/bin/env python3
"""Join the environment walk with the reference bundles into one inventory.

Inputs
  ENVWALK.tsv   output of `EnvWalk.lean` (module, line, kind, flags, name)
  BUNDLES_DIR   directory of `jaune-naming-references` bundles (one per source file)

Output (stdout, TSV): module, line, kind, flags, name, authored, referenced
  authored    y when the compiler index records a definition site for the name
              (the set the fidelity checker treats as authored constants)
  referenced  y when some source file of the tree references the constant
"""
import glob
import json
import re
import sys


def user_name(name):
    match = re.match(r'^_private\.[^.]+(?:\.[^.]+)*?\.0\.(.*)$', name)
    return match.group(1) if match else name


def main(envwalk, bundles):
    authored, referenced = set(), set()
    for path in sorted(glob.glob(bundles + '/*.json')):
        index = json.load(open(path))['index']
        for key, info in index['references'].items():
            const = json.loads(key).get('c')
            if not const:
                continue
            name = user_name(const['n'])
            referenced.add(name)
            if info.get('definition') is not None:
                authored.add(name)
    for line in open(envwalk):
        module, num, kind, flags, name = line.rstrip('\n').split('\t')
        print('\t'.join([module, num, kind, flags, name,
                         'y' if name in authored else 'n',
                         'y' if name in referenced else 'n']))


if __name__ == '__main__':
    main(*sys.argv[1:3])
