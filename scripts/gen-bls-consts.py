#!/usr/bin/env python3
"""Generate Jaune/BLSConst.lean from py_ecc's BLS12-381 constants.

Run with the frozen oracle venv associated with the configured EELS checkout:

    "$EELS_ROOT/venv/bin/python" scripts/gen-bls-consts.py \
        --execution-specs "$EELS_ROOT" --output Jaune/BLSConst.lean

Every constant needed by the EIP-2537 MAP precompiles (Step 7) is read
directly from py_ecc.optimized_bls12_381 here and emitted as plain `Nat`
(base-field elements and exponents) or `Nat × Nat` (`c0, c1` pairs for Fp2
elements).  Transcribing any of these by hand is forbidden; regenerate this
file instead.  Field-extension elements follow py_ecc's coefficient order,
constant term first: `FQ2([c0, c1])` becomes the pair `(c0, c1)`.
"""

import argparse
import sys
from pathlib import Path

import generator_common


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    generator_common.add_source_arguments(parser)
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="write generated Lean to this path instead of stdout",
    )
    return parser, parser.parse_args()


parser, args = parse_args()
manifest, execution_specs, source_root = generator_common.load_generator_source(
    parser, args.manifest, args.execution_specs
)
generator_common.require_known_packages(parser, manifest)

sys.path.insert(0, str(source_root))

from ethereum.crypto.kzg import KZG_SETUP_G2_MONOMIAL_1  # noqa: E402
from ethereum.utils.hexadecimal import hex_to_bytes  # noqa: E402
from py_ecc.bls.g2_primitives import signature_to_G2  # noqa: E402
from py_ecc.optimized_bls12_381 import constants as C  # noqa: E402
from py_ecc.optimized_bls12_381 import normalize  # noqa: E402


def fq(x):
    """A base-field element -> its integer value."""
    return x.n


def fq2(x):
    """An Fp2 element -> (c0, c1) matching py_ecc's coeffs order."""
    c0, c1 = x.coeffs
    return (int(c0), int(c1))


def nat_list(name, elems):
    body = ", ".join(str(e) for e in elems)
    return f"def {name} : List Nat := [{body}]"


def pair(p):
    return f"({p[0]}, {p[1]})"


def pair_list(name, elems):
    body = ", ".join(pair(e) for e in elems)
    return f"def {name} : List (Nat × Nat) := [{body}]"


def nat_def(name, v):
    return f"def {name} : Nat := {v}"


def pair_def(name, p):
    return f"def {name} : Nat × Nat := {pair(p)}"


out = []
w = out.append

w("-- GENERATED FILE — do not edit by hand.")
w("-- Produced by scripts/gen-bls-consts.py from py_ecc.optimized_bls12_381.")
w("-- BLS12-381 SSWU / isogeny / cofactor-clearing constants for the")
w("-- EIP-2537 map-to-curve precompiles (0x10, 0x11).")
w("--")
w("-- Base-field elements and exponents are `Nat`; Fp2 elements are")
w("-- `(c0, c1)` pairs, py_ecc coeffs order (constant term first).")
w("")
w("namespace BLSConst")
w("")

# --- G1: SSWU onto the 11-isogenous curve, then the 11-isogeny map. ---
w("-- 11-isogenous curve y^2 = x^3 + A*x + B and SSWU Z (py_ecc ISO_11_*).")
w(nat_def("iso11A", fq(C.ISO_11_A)))
w(nat_def("iso11B", fq(C.ISO_11_B)))
w(nat_def("iso11Z", fq(C.ISO_11_Z)))
w("-- sqrt(-11)^3, used to correct the SSWU y candidate (SQRT_MINUS_11_CUBED).")
w(nat_def("sqrtMinus11Cubed", fq(C.SQRT_MINUS_11_CUBED)))
w("-- (p - 3) / 4, the Fp square-root exponent.")
w(nat_def("pMinus3Div4", C.P_MINUS_3_DIV_4))
w("")
w("-- 11-isogeny map coefficients, low degree first (py_ecc order).")
w(nat_list("iso11XNum", [fq(k) for k in C.ISO_11_X_NUMERATOR]))
w(nat_list("iso11XDen", [fq(k) for k in C.ISO_11_X_DENOMINATOR]))
w(nat_list("iso11YNum", [fq(k) for k in C.ISO_11_Y_NUMERATOR]))
w(nat_list("iso11YDen", [fq(k) for k in C.ISO_11_Y_DENOMINATOR]))
w("")
w("-- G1 effective cofactor (H_EFF_G1).")
w(nat_def("hEffG1", C.H_EFF_G1))
w("")

# --- G2: SSWU onto the 3-isogenous curve, then the 3-isogeny map. ---
w("-- 3-isogenous curve y^2 = x^3 + A*x + B and SSWU Z over Fp2 (ISO_3_*).")
w(pair_def("iso3A", fq2(C.ISO_3_A)))
w(pair_def("iso3B", fq2(C.ISO_3_B)))
w(pair_def("iso3Z", fq2(C.ISO_3_Z)))
w("-- (p^2 - 9) / 16, the Fp2 square-root-division exponent.")
w(nat_def("pMinus9Div16", C.P_MINUS_9_DIV_16))
w("")
w("-- eta values and positive eighth roots of unity (Fp2 sqrt helpers).")
w(pair_list("etas", [fq2(e) for e in C.ETAS]))
w(pair_list("eighthRoots", [fq2(r) for r in C.POSITIVE_EIGHTH_ROOTS_OF_UNITY]))
w("")
w("-- 3-isogeny map coefficients, low degree first (py_ecc order).")
w(pair_list("iso3XNum", [fq2(k) for k in C.ISO_3_X_NUMERATOR]))
w(pair_list("iso3XDen", [fq2(k) for k in C.ISO_3_X_DENOMINATOR]))
w(pair_list("iso3YNum", [fq2(k) for k in C.ISO_3_Y_NUMERATOR]))
w(pair_list("iso3YDen", [fq2(k) for k in C.ISO_3_Y_DENOMINATOR]))
w("")
w("-- G2 effective cofactor (H_EFF_G2).")
w(nat_def("hEffG2", C.H_EFF_G2))
w("")

# --- EIP-4844 point-evaluation trusted-setup G2 point. ---
# The single G2 monomial (KZG_SETUP_G2_MONOMIAL_1, kzg.py:71) that
# verify_kzg_proof_impl needs; decompressed here via py_ecc into an affine
# ((x.c0, x.c1), (y.c0, y.c1)) pair in the (c0, c1) coeffs order.
setup_x, setup_y = normalize(
    signature_to_G2(hex_to_bytes(KZG_SETUP_G2_MONOMIAL_1))
)
w("-- Decompressed KZG_SETUP_G2_MONOMIAL_1 as ((x.c0, x.c1), (y.c0, y.c1)).")
w(
    "def kzgSetupG2Monomial1 : (Nat × Nat) × (Nat × Nat) := "
    f"({pair(fq2(setup_x))}, {pair(fq2(setup_y))})"
)
w("")
w("end BLSConst")

generated = "\n".join(out) + "\n"
if args.output is None:
    sys.stdout.write(generated)
else:
    args.output.write_text(generated)
    print(f"wrote BLS constants to {args.output}", file=sys.stderr)
