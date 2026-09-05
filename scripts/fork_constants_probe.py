"""Read one pinned EELS revision's fork constants, as values.

This module is executed by ``gen-fork-constants.py`` **inside the conformance
target's own virtual environment**, because the constants it reports are not
all literals: Amsterdam derives ``CREATE_ACCESS`` from two other costs,
``REFUND_STORAGE_CLEAR`` from a state-gas product, and ``MAX_INIT_CODE_SIZE``
from ``MAX_CODE_SIZE``. Scraping the source text would mean reimplementing
those expressions in a second place, which is exactly the transcription this
gate exists to remove. Importing evaluates the definitions upstream actually
ships.

The caller has already proved that the checkout's ``src/ethereum`` tree is
byte-identical to the pinned commit, so importing from the working tree reads
the pinned revision.

Every value is emitted with the dotted upstream path it came from, so the
mapping between a Jaune ``ForkRules`` field and its upstream definition is part
of the generated artifact rather than folklore in a script.
"""

from __future__ import annotations

import ast
import dataclasses
import importlib
import inspect
import json
import sys

# Jaune's `Fork.toString` label -> the EELS fork module under ethereum.forks.
FORKS = {
    "Prague": "prague",
    "Osaka": "osaka",
    "BPO1": "bpo1",
    "BPO2": "bpo2",
    "Amsterdam": "amsterdam",
}


class ProbeError(Exception):
    pass


def _mod(fork: str, suffix: str = ""):
    name = f"ethereum.forks.{fork}" + (f".{suffix}" if suffix else "")
    return importlib.import_module(name)


def _find(fork: str, name: str, modules: "tuple[str, ...]"):
    """Look a module-level constant up across the modules it may live in.

    Upstream moves constants between files without changing them --
    `BLOB_COUNT_LIMIT` is in `fork` through BPO2 and in `transactions` at
    Amsterdam, and `MAX_BLOB_GAS_PER_BLOCK` moves from `fork` to `vm.gas` --
    and the drift monitor classifies exactly that as a refactor, which is to
    say as nothing. A lookup pinned to one file would report a moved constant
    as a *changed* one, which is the opposite of what this gate is for.

    Returns `(value, source)` where `source` names the module that answered, so
    a move is visible in the generated artifact without being a failure. A
    constant no listed module defines is a real `None`: Prague has no
    `TX_MAX_GAS_LIMIT` because EIP-7825 does not exist yet, and Jaune records
    that as `tx.maxGas = none` rather than as an unbounded sentinel.
    """
    for module in modules:
        value = getattr(_mod(fork, module), name, None)
        if value is not None:
            where = f"{module}.{name}" if module else name
            return int(value), where
    searched = ", ".join(f"{m}.{name}" if m else name for m in modules)
    return None, f"absent: none of {searched} is defined at this fork"


def _require(fork: str, name: str, modules: "tuple[str, ...]"):
    value, source = _find(fork, name, modules)
    if value is None:
        raise ProbeError(f"{fork}: {source}")
    return value, source


def _opt_int(obj, name):
    value = getattr(obj, name, None)
    return None if value is None else int(value)


def _require_attr(obj, name, where):
    """Read an attribute that must exist, without converting it to an int.

    Needed where the value is a structured type rather than a number --
    upstream's `StateGasPerByte` rate, whose own field carries the number.
    """
    value = getattr(obj, name, None)
    if value is None:
        raise ProbeError(f"{where} has no {name}")
    return value


def _require_int(obj, name, where):
    value = getattr(obj, name, None)
    if value is None:
        raise ProbeError(f"{where} has no {name}")
    return int(value)


def _address_int(value) -> int:
    return int.from_bytes(bytes(value), "big")


def _code_read_surcharge(fork: str) -> tuple[int, str]:
    """EIP-8038's additive code-reading cost at EXTCODESIZE/EXTCODECOPY.

    Upstream gives this one no name: it is `GasCosts.WARM_ACCESS` added inline
    at the two opcodes, so there is nothing to look up. It is read here as a
    presence question about the source instead, which is also the honest shape
    of the fact -- before EIP-8038 the surcharge is absent, not zero-valued.
    """
    environment = _mod(fork, "vm.instructions.environment")
    source = inspect.getsource(environment)
    marker = "Code reading cost (EIP-8038)"
    if marker not in source:
        return 0, (
            "absent: vm.instructions.environment charges no EIP-8038 code-reading "
            "cost, so the surcharge is 0 by absence"
        )
    gas = _mod(fork, "vm.gas")
    return int(gas.GasCosts.WARM_ACCESS), (
        "vm.gas.GasCosts.WARM_ACCESS, added inline at extcodesize/extcodecopy "
        f"(source marker {marker!r})"
    )


# EIP-663's stack-access trio. Upstream ships the three opcodes as one
# feature and Jaune carries them as one boolean, so "some of them" is not a
# value this row can take: a fork defining only part of the trio would mean the
# feature had been split upstream and a single flag no longer modelled it.
STACK_ACCESS_OPS = ("DUPN", "SWAPN", "EXCHANGE")


def _stack_access(fork: str, ops) -> "tuple[bool, str]":
    """Whether the fork defines all of EIP-663's stack-access opcodes.

    A source-presence fact in the same style as `op.clz`, but over three names
    instead of one, so the derivation is recorded rather than left implicit. A
    partial definition raises instead of rounding to a bool: that is a drift in
    the formula this row abbreviates, and silently answering `False` (or
    `True`) would hide exactly the upstream change the gate exists to surface.
    """
    defined = [name for name in STACK_ACCESS_OPS if hasattr(ops, name)]
    derivation = (
        "vm.instructions.Ops defines all of "
        + ", ".join(STACK_ACCESS_OPS)
        + " (EIP-663)"
    )
    if not defined:
        return False, f"{derivation}: none of the three is defined at this fork"
    if len(defined) != len(STACK_ACCESS_OPS):
        missing = [name for name in STACK_ACCESS_OPS if name not in defined]
        raise ProbeError(
            f"{fork}: vm.instructions.Ops defines {defined} but not {missing}; "
            "EIP-663's stack-access opcodes are one boolean in Jaune, so a "
            "partial definition is a drift in the derivation, not a False"
        )
    return True, f"{derivation}: all three are defined"


def _requests(fork: str) -> tuple[list, str]:
    """The ordered request-producing system contracts, from the fork's own fold.

    Read out of `process_general_purpose_requests` in source order rather than
    from a list of names, because the order is the rule: the request bytes are
    concatenated in the order that function calls the contracts, and a
    reordering would be a consensus change that a set-valued read would miss.

    The receipt-derived deposit request (type 0) is deliberately not here: it
    is parsed out of the block's logs, not produced by a system call, so it is
    not one of the ordered contract calls this list models.
    """
    fork_module = _mod(fork, "fork")
    tree = ast.parse(inspect.getsource(fork_module))
    fn = next(
        (
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
            and node.name == "process_general_purpose_requests"
        ),
        None,
    )
    if fn is None:
        raise ProbeError(f"{fork}.fork has no process_general_purpose_requests")

    # Walk the body in source order, remembering the most recent
    # `target_address=NAME` and pairing it with the next `*_REQUEST_TYPE` name.
    pending_address: str | None = None
    pairs: list[tuple[str, str]] = []
    for node in _in_source_order(fn):
        if isinstance(node, ast.keyword) and node.arg == "target_address":
            if isinstance(node.value, ast.Name):
                pending_address = node.value.id
        elif isinstance(node, ast.Name) and node.id.endswith("_REQUEST_TYPE"):
            if node.id == "DEPOSIT_REQUEST_TYPE":
                continue
            if pending_address is None:
                raise ProbeError(
                    f"{fork}: {node.id} appears before any target_address"
                )
            pairs.append((pending_address, node.id))
            pending_address = None

    requests_module = _mod(fork, "requests")
    out = []
    for address_name, type_name in pairs:
        address = getattr(fork_module, address_name, None)
        if address is None:
            raise ProbeError(f"{fork}.fork has no {address_name}")
        type_bytes = getattr(requests_module, type_name, None)
        if type_bytes is None:
            raise ProbeError(f"{fork}.requests has no {type_name}")
        out.append(
            [int.from_bytes(bytes(type_bytes), "big"), f"0x{_address_int(address):040x}"]
        )
    return out, (
        "fork.process_general_purpose_requests, in source-call order: each "
        "system call's target_address paired with the request type byte its "
        "output is prefixed with"
    )


def _in_source_order(node):
    """Every descendant node, ordered by source position.

    `ast.walk` is breadth-first and therefore says nothing about order, and
    order is the whole content of the request list.
    """
    nodes = [n for n in ast.walk(node) if hasattr(n, "lineno")]
    return sorted(nodes, key=lambda n: (n.lineno, n.col_offset))



def _state_gas(fork: str) -> "list[tuple[str, dict]]":
    """Extract EIP-8037's state-gas dimension, or nulls for a fork without one.

    A fork that meters in one dimension has no `StateGasCosts` class at all, so
    every row is `null` and `stateGas.present` is `False` -- which is exactly
    what `ForkRules.stateGas = none` prints. The rows are emitted for every
    fork rather than only for the forks that have them, so the extraction's key
    set does not depend on the fork and the gate's key-set check stays a single
    comparison.

    The ten numbers live in three upstream places, and each row records which
    one answered: the state-byte counts on `StateGasCosts`, the two repriced
    execution charges and the transaction value cost on `GasCosts`, EIP-7981's
    two floor token counts as module constants of `transactions`, and the
    system-transaction reservoir as a module constant of `fork`. The three
    derived costs -- STORAGE_SET, NEW_ACCOUNT, AUTH_BASE -- are deliberately
    *not* extracted: they are products of rows already here, and Jaune computes
    them the same way, so extracting them would check an arithmetic identity
    twice instead of checking its inputs once.
    """
    gas = _mod(fork, "vm.gas")
    present = hasattr(gas, "StateGasCosts")

    def row(path, value, source):
        return (path, {"value": value, "source": source})

    if not present:
        absent = "the fork has no vm.gas.StateGasCosts: it meters in one dimension"
        paths = [
            "costPerStateByte", "stateBytesPerNewAccount",
            "stateBytesPerStorageSet", "stateBytesPerAuthBase", "storageWrite",
            "accountWrite", "txValueCost", "accessListAddressFloorTokens",
            "accessListStorageKeyFloorTokens", "systemMaxSstoresPerCall",
        ]
        return [row("stateGas.present", False,
                    "vm.gas.StateGasCosts is absent (EIP-8037 not active)")] + [
            row(f"stateGas.{name}", None, absent) for name in paths
        ]

    costs = gas.StateGasCosts
    gas_costs = gas.GasCosts
    transactions = _mod(fork, "transactions")
    fork_module = _mod(fork, "fork")
    return [
        row("stateGas.present", True,
            "vm.gas.StateGasCosts is defined (EIP-8037)"),
        # `COST_PER_STATE_BYTE` is a `StateGasPerByte`, deliberately not a
        # `Uint`: upstream models it as a *rate*, so that adding it to a gas
        # amount is a type error and only multiplying it by a byte count is
        # allowed. Its single `rate` field is the number, so that is the
        # attribute this reads, and the source string says so.
        row("stateGas.costPerStateByte",
            _require_int(
                _require_attr(costs, "COST_PER_STATE_BYTE",
                              f"{fork}.vm.gas.StateGasCosts"),
                "rate", f"{fork}.vm.gas.StateGasCosts.COST_PER_STATE_BYTE"),
            "vm.gas.StateGasCosts.COST_PER_STATE_BYTE.rate"),
        row("stateGas.stateBytesPerNewAccount",
            _require_int(costs, "STATE_BYTES_PER_NEW_ACCOUNT", f"{fork}.vm.gas.StateGasCosts"),
            "vm.gas.StateGasCosts.STATE_BYTES_PER_NEW_ACCOUNT"),
        row("stateGas.stateBytesPerStorageSet",
            _require_int(costs, "STATE_BYTES_PER_STORAGE_SET", f"{fork}.vm.gas.StateGasCosts"),
            "vm.gas.StateGasCosts.STATE_BYTES_PER_STORAGE_SET"),
        row("stateGas.stateBytesPerAuthBase",
            _require_int(costs, "STATE_BYTES_PER_AUTH_BASE", f"{fork}.vm.gas.StateGasCosts"),
            "vm.gas.StateGasCosts.STATE_BYTES_PER_AUTH_BASE"),
        row("stateGas.storageWrite",
            _require_int(gas_costs, "STORAGE_WRITE", f"{fork}.vm.gas.GasCosts"),
            "vm.gas.GasCosts.STORAGE_WRITE"),
        row("stateGas.accountWrite",
            _require_int(gas_costs, "ACCOUNT_WRITE", f"{fork}.vm.gas.GasCosts"),
            "vm.gas.GasCosts.ACCOUNT_WRITE"),
        row("stateGas.txValueCost",
            _require_int(gas_costs, "TX_VALUE_COST", f"{fork}.vm.gas.GasCosts"),
            "vm.gas.GasCosts.TX_VALUE_COST"),
        row("stateGas.accessListAddressFloorTokens",
            _require_int(transactions, "ACCESS_LIST_ADDRESS_FLOOR_TOKENS",
                         f"{fork}.transactions"),
            "transactions.ACCESS_LIST_ADDRESS_FLOOR_TOKENS"),
        row("stateGas.accessListStorageKeyFloorTokens",
            _require_int(transactions, "ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS",
                         f"{fork}.transactions"),
            "transactions.ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS"),
        row("stateGas.systemMaxSstoresPerCall",
            _require_int(fork_module, "SYSTEM_MAX_SSTORES_PER_CALL", f"{fork}.fork"),
            "fork.SYSTEM_MAX_SSTORES_PER_CALL"),
    ]


def _bal(fork: str) -> "list[tuple[str, dict]]":
    """EIP-7928's block-level access-list rules, or nulls for a fork without one.

    The same Option convention as `_state_gas`, for the same reason: both rows
    are emitted for every fork, so the extraction's key set does not depend on
    the fork and the gate's key-set check stays a single comparison. A fork
    with no block access list carries `bal.present` false and every other row
    `null`, which is exactly what `ForkRules.bal = none` prints.

    Presence is asked of the cost rather than of a class, because upstream
    gives EIP-7928 no type of its own: the per-item charge is one more member
    of `GasCosts`, absent before the EIP and present after it.
    """
    gas = _mod(fork, "vm.gas")
    costs = getattr(gas, "GasCosts", None)
    present = costs is not None and hasattr(costs, "BLOCK_ACCESS_LIST_ITEM")

    def row(path, value, source):
        return (path, {"value": value, "source": source})

    if not present:
        absent = (
            "vm.gas.GasCosts has no BLOCK_ACCESS_LIST_ITEM: the fork charges "
            "for no block access list (EIP-7928 not active)"
        )
        return [
            row("bal.present", False, absent),
            row("bal.itemCost", None, absent),
        ]
    return [
        row("bal.present", True,
            "vm.gas.GasCosts.BLOCK_ACCESS_LIST_ITEM is defined (EIP-7928)"),
        row("bal.itemCost",
            _require_int(costs, "BLOCK_ACCESS_LIST_ITEM", f"{fork}.vm.gas.GasCosts"),
            "vm.gas.GasCosts.BLOCK_ACCESS_LIST_ITEM"),
    ]


def extract(label: str, fork: str) -> dict:
    gas = _mod(fork, "vm.gas")
    costs = gas.GasCosts
    fork_module = _mod(fork, "fork")
    interpreter = _mod(fork, "vm.interpreter")
    transactions = _mod(fork, "transactions")
    mapping = _mod(fork, "vm.precompiled_contracts.mapping")
    instructions = _mod(fork, "vm.instructions")
    blocks = _mod(fork, "blocks")
    criteria = _mod(fork).FORK_CRITERIA

    header_fields = {f.name for f in dataclasses.fields(blocks.Header)}
    surcharge, surcharge_source = _code_read_surcharge(fork)
    requests, requests_source = _requests(fork)
    stack_access, stack_access_source = _stack_access(fork, instructions.Ops)

    def field(path, value, source):
        return (path, {"value": value, "source": source})

    # `createAccess` is the CREATE/CREATE2 base and the creation transaction's
    # recipient cost. Upstream spells it `OPCODE_CREATE_BASE` while the two are
    # the same number, and `CREATE_ACCESS` once EIP-8037 splits the creation
    # transaction's cost apart from the opcode's. Both names are tried, newest
    # first, and the name that answered is recorded.
    if hasattr(costs, "CREATE_ACCESS"):
        create_access, create_source = int(costs.CREATE_ACCESS), "vm.gas.GasCosts.CREATE_ACCESS"
    else:
        create_access = _require_int(costs, "OPCODE_CREATE_BASE", f"{fork}.vm.gas.GasCosts")
        create_source = "vm.gas.GasCosts.OPCODE_CREATE_BASE"

    if hasattr(costs, "EXECUTION_PER_AUTH_BASE_COST"):
        per_auth = int(costs.EXECUTION_PER_AUTH_BASE_COST)
        per_auth_source = "vm.gas.GasCosts.EXECUTION_PER_AUTH_BASE_COST"
    else:
        per_auth = _require_int(costs, "AUTH_PER_EMPTY_ACCOUNT", f"{fork}.vm.gas.GasCosts")
        per_auth_source = "vm.gas.GasCosts.AUTH_PER_EMPTY_ACCOUNT"

    # Names that live in different modules at different forks are looked up
    # across every module they are known to inhabit, newest location first.
    max_blob_gas, max_blob_gas_source = _require(
        fork, "MAX_BLOB_GAS_PER_BLOCK", ("vm.gas", "fork"))
    tx_max_gas, tx_max_gas_source = _find(
        fork, "TX_MAX_GAS_LIMIT", ("transactions", "fork"))
    blob_count, blob_count_source = _find(
        fork, "BLOB_COUNT_LIMIT", ("transactions", "fork"))
    max_rlp, max_rlp_source = _find(
        fork, "MAX_RLP_BLOCK_SIZE", ("fork", "transactions"))

    entries = [
        field("blob.target", _require_int(costs, "BLOB_TARGET_GAS_PER_BLOCK", fork),
              "vm.gas.GasCosts.BLOB_TARGET_GAS_PER_BLOCK"),
        field("blob.max", max_blob_gas, max_blob_gas_source),
        field("blob.baseFeeUpdateFraction",
              _require_int(costs, "BLOB_BASE_FEE_UPDATE_FRACTION", fork),
              "vm.gas.GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION"),
        field("blob.reserveBaseCost", _opt_int(costs, "BLOB_BASE_COST"),
              "vm.gas.GasCosts.BLOB_BASE_COST (absent before EIP-7918)"),
        field("code.maxCodeSize", _require_int(interpreter, "MAX_CODE_SIZE", fork),
              "vm.interpreter.MAX_CODE_SIZE"),
        field("code.maxInitCodeSize", _require_int(interpreter, "MAX_INIT_CODE_SIZE", fork),
              "vm.interpreter.MAX_INIT_CODE_SIZE"),
        field("tx.maxGas", tx_max_gas, tx_max_gas_source),
        field("tx.maxBlobCount", blob_count, blob_count_source),
        field("block.maxRlpSize", max_rlp, max_rlp_source),
        field("op.clz", hasattr(instructions.Ops, "CLZ"),
              "vm.instructions.Ops.CLZ is defined (EIP-7939)"),
        field("op.slotnum", hasattr(instructions.Ops, "SLOTNUM"),
              "vm.instructions.Ops.SLOTNUM is defined (EIP-7843)"),
        field("op.stackAccess", stack_access, stack_access_source),
        field("precompiles",
              sorted(_address_int(a) for a in mapping.PRE_COMPILED_CONTRACTS),
              "vm.precompiled_contracts.mapping.PRE_COMPILED_CONTRACTS keys"),
        field("gas.coldAccountAccess",
              _require_int(costs, "COLD_ACCOUNT_ACCESS", fork),
              "vm.gas.GasCosts.COLD_ACCOUNT_ACCESS"),
        field("gas.callValue", _require_int(costs, "CALL_VALUE", fork),
              "vm.gas.GasCosts.CALL_VALUE"),
        field("gas.createAccess", create_access, create_source),
        field("gas.storageClearRefund",
              _require_int(costs, "REFUND_STORAGE_CLEAR", fork),
              "vm.gas.GasCosts.REFUND_STORAGE_CLEAR"),
        field("gas.txBase", _require_int(costs, "TX_BASE", fork),
              "vm.gas.GasCosts.TX_BASE"),
        field("gas.txAccessListAddress",
              _require_int(costs, "TX_ACCESS_LIST_ADDRESS", fork),
              "vm.gas.GasCosts.TX_ACCESS_LIST_ADDRESS"),
        field("gas.txAccessListStorageKey",
              _require_int(costs, "TX_ACCESS_LIST_STORAGE_KEY", fork),
              "vm.gas.GasCosts.TX_ACCESS_LIST_STORAGE_KEY"),
        field("gas.floorTokenCost", _require_int(costs, "TX_DATA_TOKEN_FLOOR", fork),
              "vm.gas.GasCosts.TX_DATA_TOKEN_FLOOR"),
        field("gas.perAuthIntrinsic", per_auth, per_auth_source),
        field("gas.codeReadSurcharge", surcharge, surcharge_source),
        field("header.blockAccessListHash", "block_access_list_hash" in header_fields,
              "blocks.Header has a block_access_list_hash field (EIP-7928)"),
        field("header.slotNumber", "slot_number" in header_fields,
              "blocks.Header has a slot_number field (EIP-7843)"),
        field("requests", requests, requests_source),
    ] + _state_gas(fork) + _bal(fork)
    seen = [path for path, _ in entries]
    if len(seen) != len(set(seen)):
        raise ProbeError(f"{label}: duplicate field path in the extraction table")
    return {
        "label": label,
        "module": f"ethereum.forks.{fork}",
        "fork_criteria": {
            "kind": type(criteria).__name__,
            "timestamp": int(criteria.timestamp)
            if hasattr(criteria, "timestamp")
            else None,
        },
        "header_field_count": len(dataclasses.fields(blocks.Header)),
        "constants": dict(entries),
    }


def main() -> int:
    out = {label: extract(label, fork) for label, fork in FORKS.items()}
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ProbeError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
