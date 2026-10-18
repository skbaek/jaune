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
import difflib
import importlib
import inspect
import json
import re
import sys

# Jaune's `Fork.toString` label -> the EELS fork module under ethereum.forks.
FORKS = {
    "Prague": "prague",
    "Osaka": "osaka",
    "BPO1": "bpo1",
    "BPO2": "bpo2",
    "Amsterdam": "amsterdam",
}

# The pre-Prague forks, same convention. Petersburg goes through the
# `constantinople` module: mainnet never ran EIP-1283, so that module already
# carries Petersburg's rules. Jaune's EIP-1283 `Constantinople` has no module
# and is not named here; the generator synthesises its all-dormant entry.
HISTORICAL_FORKS = {
    "Byzantium": "byzantium",
    "Petersburg": "constantinople",
    "Istanbul": "istanbul",
    "MuirGlacier": "muir_glacier",
    "Berlin": "berlin",
    "London": "london",
    "ArrowGlacier": "arrow_glacier",
    "GrayGlacier": "gray_glacier",
    "Paris": "paris",
    "Shanghai": "shanghai",
    "Cancun": "cancun",
}


# Every EELS fork module from Byzantium on -> Jaune's `Fork.toString` label, for
# the mainnet schedule (design §4 of jaune-historical-forks-v1). EELS's
# `constantinople` module is Petersburg's rules (mainnet never ran EIP-1283),
# so it maps to Jaune's `Petersburg`; Jaune's `Constantinople` has no module.
SCHEDULE_FORKS = {
    "Byzantium": "byzantium",
    "Petersburg": "constantinople",
    "Istanbul": "istanbul",
    "MuirGlacier": "muir_glacier",
    "Berlin": "berlin",
    "London": "london",
    "ArrowGlacier": "arrow_glacier",
    "GrayGlacier": "gray_glacier",
    "Paris": "paris",
    "Shanghai": "shanghai",
    "Cancun": "cancun",
    "Prague": "prague",
    "Osaka": "osaka",
    "BPO1": "bpo1",
    "BPO2": "bpo2",
    "Amsterdam": "amsterdam",
}


class ProbeError(Exception):
    pass


def criterion_value(criteria):
    """A `FORK_CRITERIA` as the gate compares it: a timestamp as a bare
    integer (the `mainnetActivation` row's shape since D13), a block number as
    `{"block": n}`, and anything else (`Unscheduled`) as `None`."""
    if hasattr(criteria, "timestamp"):
        return int(criteria.timestamp)
    if hasattr(criteria, "block_number"):
        return {"block": int(criteria.block_number)}
    return None


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


# Historical-lookup misses, collected across every fork and field so that one
# generator run reports the complete repair list instead of stopping at the
# first unknown name. `main` refuses to emit JSON while any miss is recorded.
_MISSES: "list[str]" = []


def _close_names(haystack, names: "tuple[str, ...]", limit: int = 8) -> list:
    try:
        candidates = [n for n in dir(haystack) if not n.startswith("_")]
    except Exception:
        return []
    close: list = []
    for name in names:
        close.extend(difflib.get_close_matches(name, candidates, n=limit))
    return sorted(set(close))


def _hist_cost(costs, fork: str, names: "tuple[str, ...]", where: str):
    """A live historical number: the first candidate name that answers.

    Every candidate is tried because upstream renames costs between eras; the
    name that answered is recorded, so a rename is visible in the artifact.
    A total miss is collected (with close matches) rather than raised, so one
    run names every unknown across all forks.
    """
    for name in names:
        value = getattr(costs, name, None)
        if value is not None:
            return int(value), f"{where}.{name}"
    _MISSES.append(
        f"{fork}: none of {list(names)} in {where}; "
        f"closest: {_close_names(costs, names)}"
    )
    return None, "UNRESOLVED: see the probe miss report"


def _hist_mod(fork: str, names: "tuple[str, ...]", modules: "tuple[str, ...]"):
    """Module-level variant of `_hist_cost`, for fork-level constants."""
    for name in names:
        for module in modules:
            try:
                owner = _mod(fork, module)
            except ImportError:
                continue
            value = getattr(owner, name, None)
            if value is not None:
                where = f"{module}.{name}" if module else name
                return int(value), where
    try:
        owner = _mod(fork, modules[0])
    except ImportError:
        owner = None
    _MISSES.append(
        f"{fork}: none of {list(names)} in {list(modules)}; "
        f"closest: {_close_names(owner, names) if owner is not None else []}"
    )
    return None, "UNRESOLVED: see the probe miss report"


def _hist_opt(costs, fork: str, name: str, where: str):
    """A possibly-absent historical number: `None` by absence, never a miss."""
    value = getattr(costs, name, None)
    if value is None:
        return None, f"absent: {where}.{name} is not defined at this fork"
    return int(value), f"{where}.{name}"


def _hist_blob(costs, fork_module, fork: str, names: "tuple[str, ...]"):
    """One blob-schedule number on the historical path (goal U10).

    Searched on `GasCosts` first, then at module level: Cancun keeps its
    schedule in whichever place answers, and only Cancun must answer at
    all, because only Cancun meters blobs. Any earlier fork reports absence
    (its three cells are dormant); Cancun collects a miss instead.
    """
    for name in names:
        value = getattr(costs, name, None)
        if value is not None:
            return int(value), f"vm.gas.GasCosts.{name}"
    for module in ("vm.gas", "fork"):
        owner = _mod(fork, module) if module != "fork" else fork_module
        for name in names:
            value = getattr(owner, name, None)
            if value is not None:
                return int(value), f"{module}.{name}"
    if fork == "cancun":
        _MISSES.append(
            f"{fork}: none of {list(names)} on vm.gas.GasCosts or at module "
            f"level; closest: {_close_names(costs, names)}"
        )
        return None, "UNRESOLVED: see the probe miss report"
    return None, (
        f"absent: none of {list(names)} is defined at this fork "
        "(pre-EIP-4844): no blob schedule"
    )


def tx_base_entry(costs, fork: str, historical: bool) -> "tuple[int | None, str]":
    """The intrinsic cost every transaction pays (goal U10 helper).

    21,000 at every fork Jaune names; the modern path requires the modern
    name, the historical path collects a miss instead of raising.
    """
    if not historical:
        return (
            _require_int(costs, "TX_BASE", fork),
            "vm.gas.GasCosts.TX_BASE",
        )
    return _hist_cost(
        costs, fork, ("TX_BASE", "GAS_TX", "GAS_TRANSACTION"),
        "vm.gas.GasCosts")


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


def _requests(fork: str, historical: bool = False) -> tuple[list, str]:
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
        if historical:
            return [], (
                "absent: fork.fork has no process_general_purpose_requests "
                "(pre-Prague): no request-producing system calls"
            )
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


# U1c: the eleven pre-Osaka opcode flags. Each is a source-presence fact in
# the same style as `op.clz`: whether `vm.instructions.Ops` defines the
# member. Flags that activate together are read together -- EIP-145 assigns
# SHL/SHR/SAR as one feature and EIP-1153 TLOAD/TSTORE as one -- and, as with
# `_stack_access`, a partial definition raises instead of rounding to a bool.
_OPCODE_SINGLES = (
    ("op.extCodeHash", "EXTCODEHASH", "EIP-1052"),
    ("op.create2", "CREATE2", "EIP-1014"),
    ("op.chainId", "CHAINID", "EIP-1344"),
    ("op.selfBalance", "SELFBALANCE", "EIP-1884"),
    ("op.baseFee", "BASEFEE", "EIP-3198"),
    ("op.push0", "PUSH0", "EIP-3855"),
    ("op.mcopy", "MCOPY", "EIP-5656"),
    ("op.blobHash", "BLOBHASH", "EIP-4844"),
    ("op.blobBaseFee", "BLOBBASEFEE", "EIP-7516"),
)

_OPCODE_GROUPS = (
    ("op.shifts", ("SHL", "SHR", "SAR"), "EIP-145"),
    ("op.transient", ("TLOAD", "TSTORE"), "EIP-1153"),
)


def _all_or_none(fork: str, names: "tuple[str, ...]", eip: str, where: str,
                 present) -> "tuple[bool, str]":
    """One boolean over several names that activate together.

    Both extremes are values; a partial definition raises, because the
    feature was split upstream and a single flag no longer models it.
    """
    defined = [name for name in names if present(name)]
    tag = ", ".join(names)
    if len(defined) == len(names):
        return True, f"{where} defines all of {tag} ({eip})"
    if not defined:
        return False, f"{where} defines none of {tag} ({eip})"
    missing = [name for name in names if name not in defined]
    raise ProbeError(
        f"{fork}: {where} defines {defined} but not {missing}; "
        f"{eip} assigns them together, so a partial definition is drift, "
        "not a boolean"
    )


def _opcodes(fork: str, ops) -> "list[tuple[str, dict]]":
    """The eleven pre-Osaka opcode-availability flags (goal U1)."""
    rows = []
    for path, member, eip in _OPCODE_SINGLES:
        value = hasattr(ops, member)
        rows.append((path, {
            "value": value,
            "source": f"vm.instructions.Ops.{member} is defined ({eip})",
        }))
    for path, members, eip in _OPCODE_GROUPS:
        value, source = _all_or_none(
            fork, members, eip, "vm.instructions.Ops",
            lambda name: hasattr(ops, name))
        rows.append((path, {"value": value, "source": source}))
    return rows


# U1c: the five pre-Prague header flags. `blobGas` is one boolean over the
# two EIP-4844 fields, which activate together.
_HEADER_SINGLES = (
    ("header.baseFee", "base_fee_per_gas", "EIP-1559"),
    ("header.withdrawalsRoot", "withdrawals_root", "EIP-4895"),
    ("header.parentBeaconBlockRoot", "parent_beacon_block_root", "EIP-4788"),
    ("header.requestsHash", "requests_hash", "EIP-7685"),
)


def _headers(fork: str, header_fields) -> "list[tuple[str, dict]]":
    """The five pre-Prague header-presence flags (goal U1)."""
    rows = []
    for path, field_name, eip in _HEADER_SINGLES:
        value = field_name in header_fields
        rows.append((path, {
            "value": value,
            "source": f"blocks.Header has a {field_name} field ({eip})",
        }))
    value, source = _all_or_none(
        fork, ("blob_gas_used", "excess_blob_gas"), "EIP-4844",
        "blocks.Header", lambda name: name in header_fields)
    rows.append(("header.blobGas", {"value": value, "source": source}))
    return rows


def _access(fork: str, historical: bool = False) -> "list[tuple[str, dict]]":
    """The access-pricing shape and its flat prices (goal U1, U10).

    A fork with the EIP-2929 warm/cold schedule prices access that way, so
    the shape is `eip2929` and the five flat prices are `null` -- exactly
    what `ForkRules.access = .eip2929` prints. A pre-Berlin fork carries the
    flat EIP-150/EIP-1884 prices instead, read as values with the dotted
    path that answered (upstream renames them between eras; the name that
    answered is recorded). A total miss is collected, not raised.
    """
    costs = _mod(fork, "vm.gas").GasCosts
    if hasattr(costs, "WARM_ACCESS") and hasattr(costs, "COLD_ACCOUNT_ACCESS"):
        source = (
            "vm.gas.GasCosts defines WARM_ACCESS and COLD_ACCOUNT_ACCESS "
            "(EIP-2929): access is warm/cold priced, so there are no flat "
            "prices to print"
        )
        rows = [("access.shape", {"value": "eip2929", "source": source})]
        for name in ("balance", "extCode", "extCodeHash", "sload", "call"):
            rows.append((f"access.{name}", {"value": None, "source": source}))
        return rows
    if not historical:
        raise ProbeError(
            f"{fork}: no EIP-2929 warm/cold schedule in vm.gas.GasCosts; "
            "flat access prices need historical extraction (U10)"
        )
    # Pre-Berlin flat prices (goal U10). One number per opcode family, no
    # warm/cold distinction; the accessed sets are not consulted for gas.
    # The era names are tried first; a family with no answer collects the
    # keyword-filtered member list for classification, so one run reports
    # the real names instead of stopping at a guess.
    rows = [("access.shape", {
        "value": "flat",
        "source": "vm.gas.GasCosts has no WARM_ACCESS/COLD_ACCOUNT_ACCESS "
        "(pre-EIP-2929): access is flat priced",
    })]
    # Observed era names (byzantium/constantinople/istanbul listings): the
    # per-opcode base costs are OPCODE_* (OPCODE_BALANCE is the BALANCE price,
    # not the opcode number), the external-code base is OPCODE_EXTERNAL_BASE,
    # EXTCODEHASH is OPCODE_EXTCODEHASH (absent before EIP-1052), SLOAD is
    # bare SLOAD, and CALL is OPCODE_CALL_BASE. The name that answered is
    # recorded; a miss collects the keyword-filtered member list.
    members = sorted(n for n in dir(costs) if not n.startswith("_"))
    for path, keyword, names, optional in (
        ("access.balance", "BALANCE", ("OPCODE_BALANCE",), False),
        ("access.extCode", "EXTCODE", ("OPCODE_EXTERNAL_BASE",), False),
        ("access.extCodeHash", "EXTCODEHASH", ("OPCODE_EXTCODEHASH",), True),
        ("access.sload", "SLOAD", ("SLOAD",), False),
        ("access.call", "CALL", ("OPCODE_CALL_BASE",), False),
    ):
        found = None
        for name in names:
            value = getattr(costs, name, None)
            if value is not None:
                found = (int(value), f"vm.gas.GasCosts.{name}")
                break
        if found is None:
            if optional:
                found = (None, (
                    f"absent: vm.gas.GasCosts has no {names[0]} "
                    "(pre-EIP-1052): the opcode is undefined at this fork"
                ))
            else:
                _MISSES.append(
                    f"{fork}: {path} answers none of {list(names)}; "
                    f"GasCosts members containing {keyword!r}: "
                    f"{sorted(n for n in members if keyword in n)}"
                )
                found = (None, "UNRESOLVED: see the probe miss report")
        value, source = found
        rows.append((path, {"value": value, "source": source}))
    return rows


def _sstore(fork: str) -> "list[tuple[str, dict]]":
    """The SSTORE shape: net metering and the stipend sentry (goal U1).

    Both are source-presence facts about `sstore`. Net metering needs the
    slot's transaction-start value, so it is the `get_storage_original`
    read (EIP-1283's rule, kept through EIP-2200 and EIP-2929); the sentry
    is the `CALL_STIPEND` check (EIP-2200, Istanbul onwards).
    """
    source = inspect.getsource(_mod(fork, "vm.instructions.storage").sstore)
    net = "get_storage_original" in source
    sentry = "CALL_STIPEND" in source
    return [
        ("sstore.netMetering", {
            "value": net,
            "source": "vm.instructions.storage.sstore reads "
            "get_storage_original (EIP-1283/2200/2929 net metering)",
        }),
        ("sstore.stipendSentry", {
            "value": sentry,
            "source": "vm.instructions.storage.sstore checks "
            "GasCosts.CALL_STIPEND (EIP-2200 stipend sentry)",
        }),
    ]


def _refund_quotient(fork: str) -> "tuple[int, str]":
    """The refund cap's divisor: the `// Uint(N)` in the refund computation.

    Upstream gives the fifth-cap no name -- Prague through BPO2 write
    `tx_gas_used_before_refund // Uint(5)` in `fork.py`, Amsterdam writes
    `gas_used_before_refund // Uint(5)` in `vm.gas.settle_transaction_gas`
    -- so it is read as the divisor literal, in the same spirit as the
    code-reading surcharge. Both candidate modules are searched and the
    distinct values must agree; anything else is drift, not a number.
    """
    found: dict[int, str] = {}
    for suffix in ("fork", "vm.gas"):
        module = _mod(fork, suffix)
        module_source = inspect.getsource(module)
        tree = ast.parse(module_source)
        for node in ast.walk(tree):
            if not (isinstance(node, ast.BinOp)
                    and isinstance(node.op, ast.FloorDiv)):
                continue
            left = ast.get_source_segment(module_source, node.left) or ""
            right = node.right
            if "before_refund" not in left:
                continue
            if (isinstance(right, ast.Call)
                    and isinstance(right.func, ast.Name)
                    and right.func.id == "Uint"
                    and len(right.args) == 1
                    and isinstance(right.args[0], ast.Constant)):
                value = int(right.args[0].value)
                found.setdefault(value, f"{suffix} (line {node.lineno})")
    if len(found) != 1:
        raise ProbeError(
            f"{fork}: refund divisor is not one literal: {found or 'none found'}"
        )
    value = next(iter(found))
    return value, (
        f"the refund computation divides pre-refund usage by Uint({value}) "
        f"({found[value]}, EIP-3529 fifth-cap)"
    )


def _selfdestruct_refund(fork: str, historical: bool = False) -> "tuple[int | None, str]":
    """The SELFDESTRUCT gas refund: zero by absence since EIP-3529 (goal U1, U10).

    Either a named refund constant answers, in which case its value is the
    row, or no constant and no refund in `selfdestruct`'s source means the
    refund is gone and the row is 0. A refund through any other path
    raises rather than rounding to 0 -- on the historical path by collecting
    the refund-named constants for classification, so one run reports them.

    The modern path is byte-identical to the pre-U10 probe: module-level
    lookup first, then the source check. Only the historical path tries the
    era names on `GasCosts`.
    """
    if not historical:
        value, source = _find(
            fork, "REFUND_SELF_DESTRUCT", ("vm.gas", "fork", "transactions"))
        if value is not None:
            return value, source
        system = _mod(fork, "vm.instructions.system")
        selfdestruct_source = inspect.getsource(system.selfdestruct)
        if "refund" in selfdestruct_source.lower():
            raise ProbeError(
                f"{fork}: vm.instructions.system.selfdestruct mentions a refund "
                "but no REFUND_SELF_DESTRUCT constant names it; classify by hand"
            )
        return 0, (
            "absent: no REFUND_SELF_DESTRUCT in vm.gas, fork or transactions, "
            "and vm.instructions.system.selfdestruct grants none (EIP-3529)"
        )
    names = ("REFUND_SELF_DESTRUCT", "GAS_SELFDESTRUCT_REFUND", "SELFDESTRUCT_REFUND")
    costs = _mod(fork, "vm.gas").GasCosts
    for name in names:
        value = getattr(costs, name, None)
        if value is not None:
            return int(value), f"vm.gas.GasCosts.{name}"
    value, source = _find(
        fork, "REFUND_SELF_DESTRUCT", ("vm.gas", "fork", "transactions"))
    if value is not None:
        return value, source
    system = _mod(fork, "vm.instructions.system")
    selfdestruct_source = inspect.getsource(system.selfdestruct)
    if "refund" not in selfdestruct_source.lower():
        return 0, (
            "absent: no refund constant in vm.gas, fork or transactions, "
            "and vm.instructions.system.selfdestruct grants none (EIP-3529)"
        )
    refund_names = sorted(
        {n for n in dir(costs) if "REFUND" in n}
        | {n for module in ("fork", "transactions")
           for n in dir(_mod(fork, module)) if "REFUND" in n}
    )
    _MISSES.append(
        f"{fork}: vm.instructions.system.selfdestruct grants a refund "
        f"but none of {list(names)} names it; refund-named constants: "
        f"{refund_names}"
    )
    return None, "UNRESOLVED: see the probe miss report"


def _settle(fork: str, fork_module, historical: bool = False) -> "list[tuple[str, dict]]":
    """The settlement numbers and switches (goal U1, U10)."""
    quotient, quotient_source = _refund_quotient(fork)
    refund, refund_source = _selfdestruct_refund(fork, historical)
    system_source = inspect.getsource(
        _mod(fork, "vm.instructions.system").selfdestruct)
    only_created = "same transaction" in system_source
    fork_source = inspect.getsource(fork_module)
    sweep = "touched" in fork_source.lower()
    state_module = None
    try:
        state_module = _mod(fork, "state")
    except ImportError:
        pass
    if state_module is not None:
        sweep = sweep or "touched" in inspect.getsource(state_module).lower()
    # `modify_state` (goal U6b): from Paris it destroys an account the
    # modification leaves empty; before Paris it is `set_account` alone.
    erase_module = None
    for name in ("state_tracker", "state"):
        try:
            erase_module = _mod(fork, name)
        except ImportError:
            continue
        if hasattr(erase_module, "modify_state"):
            break
        erase_module = None
    if erase_module is None:
        raise SystemExit(f"{fork}: no state module defines modify_state")
    erase = "destroy_account" in inspect.getsource(erase_module.modify_state)
    return [
        ("settle.refundQuotient",
         {"value": quotient, "source": quotient_source}),
        ("settle.selfdestructRefund",
         {"value": refund, "source": refund_source}),
        ("settle.selfdestructOnlyCreated", {
            "value": only_created,
            "source": "vm.instructions.system.selfdestruct deletes only an "
            "account created in the same transaction (EIP-6780)",
        }),
        ("settle.touchedSweep", {
            "value": sweep,
            "source": "absent: fork applies no touched-empty sweep "
            "(EIP-161 sweep dropped at Paris)",
        }),
        ("settle.eraseEmptyOnModify", {
            "value": erase,
            "source": f"{erase_module.__name__}.modify_state calls "
            "destroy_account on an emptied account",
        }),
    ]


def _max_type(fork: str, historical: bool = False) -> "tuple[int, str]":
    """The largest admitted EIP-2718 type, from `decode_transaction`.

    The type bytes are read out of the `tx[0] == N` dispatch in source
    order, paired with the class each branch decodes to -- the order is
    irrelevant here, only the largest byte matters, but recording the
    mapping is what makes a new type visible in the artifact. Legacy
    type 0 is bare RLP (the `else` branch), never a dispatch byte.

    Berlin (goal U10) guards the single typed branch the other way round
    (`tx[0] != 1` raises, then decodes): with no `==` dispatch at all, the
    `!=` byte is the largest admitted type. That fallback runs only when
    the `==` search finds nothing, so the modern forks' rows are unchanged.
    """
    transactions = _mod(fork, "transactions")
    tree = ast.parse(inspect.getsource(transactions))
    fn = next(
        (
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
            and node.name == "decode_transaction"
        ),
        None,
    )
    if fn is None:
        raise ProbeError(f"{fork}.transactions has no decode_transaction")
    mapping: dict[int, str] = {}
    pending: int | None = None
    for node in _in_source_order(fn):
        if (isinstance(node, ast.Compare) and len(node.ops) == 1
                and isinstance(node.ops[0], ast.Eq)):
            left, compared = node.left, node.comparators[0]
            if (isinstance(left, ast.Subscript)
                    and isinstance(compared, ast.Constant)
                    and isinstance(compared.value, int)):
                pending = compared.value
        elif (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "decode_to"
                and node.args
                and isinstance(node.args[0], ast.Name)
                and pending is not None):
            mapping.setdefault(pending, node.args[0].id)
            pending = None
    if not mapping:
        if not historical:
            raise ProbeError(
                f"{fork}: decode_transaction has no tx[0] == N dispatch"
            )
        guarded: list[int] = []
        for node in _in_source_order(fn):
            if (isinstance(node, ast.Compare) and len(node.ops) == 1
                    and isinstance(node.ops[0], ast.NotEq)):
                left, compared = node.left, node.comparators[0]
                if (isinstance(left, ast.Subscript)
                        and isinstance(compared, ast.Constant)
                        and isinstance(compared.value, int)):
                    guarded.append(compared.value)
        if not guarded:
            raise ProbeError(
                f"{fork}: decode_transaction has neither a tx[0] == N "
                "dispatch nor a tx[0] != N guard"
            )
        return max(guarded), (
            "transactions.decode_transaction guards type bytes "
            f"{sorted(guarded)} with tx[0] != N (Berlin shape: the single "
            "typed branch decodes, anything else raises; legacy type 0 is "
            "bare RLP)"
        )
    pairs = ", ".join(f"{byte}: {name}"
                      for byte, name in sorted(mapping.items()))
    return max(mapping), (
        "transactions.decode_transaction dispatches type bytes "
        f"{{{pairs}}} (legacy type 0 is bare RLP)"
    )


def _data_nonzero(fork: str) -> "tuple[int, str]":
    """The per-nonzero-byte data cost: tokens times the token price (goal U1).

    Since EIP-7623 a nonzero byte costs tokens, not gas directly:
    `tokens_in_calldata = num_zeros + num_non_zeros * Uint(N)` in
    `transactions.py`, each token priced at
    `vm.gas.GasCosts.TX_DATA_TOKEN_STANDARD`. The row is the product;
    the derivation is the source string, not a second implementation.
    """
    standard = _require_int(
        _mod(fork, "vm.gas").GasCosts, "TX_DATA_TOKEN_STANDARD",
        f"{fork}.vm.gas.GasCosts")
    source = inspect.getsource(_mod(fork, "transactions"))
    mults = {int(match.group(1)) for match in
             re.finditer(r"num_non_zeros \* Uint\((\d+)\)", source)}
    if len(mults) != 1:
        raise ProbeError(
            f"{fork}: nonzero-byte tokenisation is not one literal: "
            f"{sorted(mults) or 'none found'}"
        )
    tokens = mults.pop()
    return tokens * standard, (
        f"transactions tokenises a nonzero byte as {tokens} tokens "
        f"(num_non_zeros * Uint({tokens})) at "
        f"vm.gas.GasCosts.TX_DATA_TOKEN_STANDARD ({standard})"
    )


def _warm_coinbase(fork: str, fork_module) -> "tuple[bool, str]":
    """Whether the coinbase starts warm (EIP-3651, goal U1).

    Prague through BPO2 add it to the transaction's access-list addresses
    in `fork.py`; Amsterdam warms it into the frame's accessed addresses in
    `vm.interpreter` instead. Either site answers; neither means cold.
    """
    if "access_list_addresses.add(block_env.coinbase)" in inspect.getsource(
            fork_module):
        return True, (
            "fork warms block_env.coinbase into the access-list "
            "addresses (EIP-3651)"
        )
    interpreter_source = inspect.getsource(_mod(fork, "vm.interpreter"))
    if "accessed_addresses.add(block_env.coinbase)" in interpreter_source:
        return True, (
            "vm.interpreter warms block_env.coinbase into the frame's "
            "accessed addresses (EIP-3651)"
        )
    return False, (
        "absent: neither fork nor vm.interpreter warms the coinbase"
    )


def _data_nonzero_hist(fork: str, gas_costs) -> "tuple[int | None, str]":
    """The pre-EIP-7623 per-nonzero-byte data cost (goal U10).

    Before Prague a nonzero byte costs gas directly, as one flat constant
    (68, then 16 after EIP-2028 in Istanbul). The name that answered is
    recorded; a total miss is collected with close matches.
    """
    names = (
        "GAS_TXDATANONZERO", "TXDATANONZERO", "GAS_TX_DATA_NON_ZERO",
        "TX_DATA_NON_ZERO", "TX_DATA_PER_NON_ZERO",
    )
    for name in names:
        value = getattr(gas_costs, name, None)
        if value is not None:
            return int(value), f"vm.gas.GasCosts.{name}"
    owners = []
    for module in ("transactions", "fork"):
        try:
            owners.append((module, _mod(fork, module)))
        except ImportError:
            continue
    for module, owner in owners:
        for name in names:
            value = getattr(owner, name, None)
            if value is not None:
                return int(value), f"{module}.{name}"
    close = sorted(
        set(_close_names(gas_costs, names))
        | {c for _, owner in owners for c in _close_names(owner, names)}
    )
    _MISSES.append(
        f"{fork}: none of {list(names)} in vm.gas.GasCosts, transactions "
        f"or fork; closest: {close}"
    )
    return None, "UNRESOLVED: see the probe miss report"


# Fork modules (not labels) without typed transactions: only legacy type 0,
# so the largest admitted type is 0 by absence rather than by dispatch.
_PRE_TYPED_TXN = ("byzantium", "constantinople", "istanbul", "muir_glacier")


def _txr(fork: str, fork_module, historical: bool = False) -> "list[tuple[str, dict]]":
    """The transaction admission and intrinsic-cost switches (goal U1, U10)."""
    if historical:
        try:
            max_type, max_type_source = _max_type(fork, historical=True)
        except ProbeError:
            if fork in _PRE_TYPED_TXN:
                max_type, max_type_source = 0, (
                    "absent: transactions.decode_transaction has no "
                    "tx[0] == N dispatch (pre-EIP-2930): only legacy type 0"
                )
            else:
                try:
                    tx_module_source = inspect.getsource(_mod(fork, "transactions"))
                    tree = ast.parse(tx_module_source)
                    fn = next(
                        (
                            node
                            for node in ast.walk(tree)
                            if isinstance(node, ast.FunctionDef)
                            and node.name == "decode_transaction"
                        ),
                        None,
                    )
                    if fn is not None:
                        segment = ast.get_source_segment(tx_module_source, fn)
                        tx_source = segment[:3000] if segment else "<empty segment>"
                    else:
                        tx_source = "<no decode_transaction function>"
                except Exception:
                    tx_source = "<transactions source unreadable>"
                _MISSES.append(
                    f"{fork}: typed-era decode_transaction has an unknown "
                    f"dispatch shape; decode_transaction source:\n{tx_source}"
                )
                max_type, max_type_source = None, "UNRESOLVED: see the probe miss report"
        data_nonzero, data_nonzero_source = _data_nonzero_hist(
            fork, _mod(fork, "vm.gas").GasCosts)
    else:
        max_type, max_type_source = _max_type(fork)
        data_nonzero, data_nonzero_source = _data_nonzero(fork)
    transactions = _mod(fork, "transactions")
    if hasattr(transactions, "IntrinsicGasCost"):
        intrinsic_fields = {f.name for f in dataclasses.fields(
            transactions.IntrinsicGasCost)}
        floor = "calldata_floor" in intrinsic_fields
        floor_source = (
            "transactions.IntrinsicGasCost has a calldata_floor field "
            "(EIP-7623)"
        )
    else:
        # No intrinsic-cost record at all: the EIP-7623 floor cannot exist
        # where its record does not. Pre-Prague Jaune carries False.
        floor, floor_source = False, (
            "absent: transactions has no IntrinsicGasCost (pre-EIP-7623): "
            "no calldata floor"
        )
    warm, warm_source = _warm_coinbase(fork, fork_module)
    return [
        ("txr.maxType", {"value": max_type, "source": max_type_source}),
        ("txr.dataNonZero",
         {"value": data_nonzero, "source": data_nonzero_source}),
        ("txr.calldataFloor", {
            "value": floor,
            "source": floor_source,
        }),
        ("txr.warmCoinbase", {"value": warm, "source": warm_source}),
    ]


def _creation(fork: str, interpreter) -> "list[tuple[str, dict]]":
    """The creation-time switches (goal U1).

    `initCodeLimit` is whether `MAX_INIT_CODE_SIZE` exists to enforce
    (EIP-3860, the same site `code.maxInitCodeSize` reads); `rejectEf` is
    whether the interpreter refuses `0xEF`-leading deposited code
    (EIP-3541).
    """
    limit = hasattr(interpreter, "MAX_INIT_CODE_SIZE")
    reject = "0xEF" in inspect.getsource(interpreter)
    return [
        ("creation.initCodeLimit", {
            "value": limit,
            "source": "vm.interpreter.MAX_INIT_CODE_SIZE is defined "
            "(EIP-3860)",
        }),
        ("creation.rejectEf", {
            "value": reject,
            "source": "vm.interpreter refuses 0xEF-leading deposited code "
            "(EIP-3541)",
        }),
    ]


def _pow(fork: str, fork_module, historical: bool = False) -> "list[tuple[str, dict]]":
    """The proof-of-work numbers, or nulls for a post-merge fork (goal U1, U10).

    The same Option convention as `_state_gas`: a fork whose seal left the
    execution layer carries `pow.present` false and both numbers `null`,
    exactly as `ForkRules.pow = none` prints. A pre-merge historical fork
    still defines a block reward and a bomb delay, read as values with the
    dotted path that answered (goal U10; the bomb-only forks differ only
    here, so this row is their whole evidence).
    """
    if not hasattr(fork_module, "BLOCK_REWARD"):
        absent = (
            "fork.fork has no BLOCK_REWARD: the seal left the execution layer "
            "at the merge, so there is no reward or bomb delay to print"
        )
        return [
            ("pow.present", {
                "value": False,
                "source": absent,
            }),
            ("pow.blockReward", {"value": None, "source": absent}),
            ("pow.bombDelay", {"value": None, "source": absent}),
        ]
    if not historical:
        raise ProbeError(
            f"{fork}: fork.BLOCK_REWARD is defined but Jaune carries "
            "pow = none; read the numbers instead of nulling them"
        )
    reward, reward_source = _hist_mod(
        fork, ("BLOCK_REWARD",), ("fork",))
    delay, delay_source = _hist_mod(
        fork,
        ("BOMB_DELAY_BLOCKS", "BOMB_DELAY", "DIFFICULTY_BOMB_DELAY"),
        ("fork",))
    return [
        ("pow.present", {
            "value": True,
            "source": "fork.fork defines BLOCK_REWARD: the seal is still "
            "proof of work",
        }),
        ("pow.blockReward", {"value": reward, "source": reward_source}),
        ("pow.bombDelay", {"value": delay, "source": delay_source}),
    ]


def _sys(fork: str, fork_module) -> "list[tuple[str, dict]]":
    """The pre-transaction system calls (goal U1).

    Each flag is whether the fork's system-call address is both defined and
    actually called as a `target_address`: EIP-4788's beacon roots and
    EIP-2935's history storage. A defined-but-uncalled address raises
    rather than rounding to either boolean.
    """
    fork_source = inspect.getsource(fork_module)
    rows = []
    for path, address, eip in (
        ("sys.beaconRoots", "BEACON_ROOTS_ADDRESS", "EIP-4788"),
        ("sys.historyStorage", "HISTORY_STORAGE_ADDRESS", "EIP-2935"),
    ):
        defined = hasattr(fork_module, address)
        called = re.search(
            rf"target_address\s*=\s*{address}\b", fork_source) is not None
        if defined != called:
            raise ProbeError(
                f"{fork}: fork.{address} is "
                f"{'defined but never called' if defined else 'called but not defined'}"
                f" ({eip}); classify by hand"
            )
        rows.append((path, {
            "value": defined,
            "source": f"fork.{address} is defined and called as a "
            f"system-call target_address ({eip})",
        }))
    return rows


def _bn254(fork: str, historical: bool = False) -> "list[tuple[str, dict]]":
    """The alt_bn128 precompile prices, repriced by EIP-1108 (goal U1, U10).

    Read off `vm.gas.GasCosts`, where the precompile functions charge
    them: add and mul directly, the pairing as base plus per-point. On the
    historical path every era name is tried and the winner recorded; a total
    miss is collected, not raised.
    """
    costs = _mod(fork, "vm.gas").GasCosts
    rows = []
    for path, names in (
        ("bn254.add", ("PRECOMPILE_ECADD", "GAS_ECADD")),
        ("bn254.mul", ("PRECOMPILE_ECMUL", "GAS_ECMUL")),
        ("bn254.pairingBase",
         ("PRECOMPILE_ECPAIRING_BASE", "GAS_ECPAIRING_BASE")),
        ("bn254.pairingPerPair",
         ("PRECOMPILE_ECPAIRING_PER_POINT", "GAS_ECPAIRING_PER_POINT")),
    ):
        if historical:
            value, source = _hist_cost(costs, fork, names, "vm.gas.GasCosts")
            rows.append((path, {"value": value, "source": source}))
        else:
            rows.append((path, {
                "value": _require_int(costs, names[0], f"{fork}.vm.gas.GasCosts"),
                "source": f"vm.gas.GasCosts.{names[0]}",
            }))
    return rows


def _modexp_complexity(fork: str, historical: bool = False) -> "tuple[str, str]":
    """Which MODEXP complexity formula the fork prices (goal U1, U10).

    EIP-2565 sizes words as `words ** 2` with `words = (length + 7) // 8`;
    EIP-198's piecewise polynomial sizes `word_count` instead. The EIP-2565
    spelling is checked first because it is the newer one; a historical fork
    with the older shape answers `eip198`. Any other shape raises rather
    than guessing -- on the historical path by collecting the complexity
    function's source for classification, so one run reports it.
    """
    modexp_module = _mod(fork, "vm.precompiled_contracts.modexp")
    source = inspect.getsource(modexp_module)
    if "words **" in source:
        return "eip2565", (
            "vm.precompiled_contracts.modexp.complexity sizes words as "
            "words**2 (EIP-2565), not the EIP-198 piecewise polynomial"
        )
    if historical and "word_count" in source:
        return "eip198", (
            "vm.precompiled_contracts.modexp.complexity sizes word_count "
            "through the piecewise polynomial (EIP-198, pre-Berlin)"
        )
    if historical and "max_length" in source:
        return "eip198", (
            "vm.precompiled_contracts.modexp.complexity sizes max_length "
            "through the EIP-198 piecewise polynomial "
            "(max_length**2 up to 64 words; the observed shape)"
        )
    if historical:
        fn = getattr(modexp_module, "complexity", None)
        body = inspect.getsource(fn)[:1200] if fn is not None else "<no complexity function>"
        _MISSES.append(
            f"{fork}: unrecognised MODEXP complexity shape; "
            f"complexity source:\n{body}"
        )
        return "UNRESOLVED", "see the probe miss report"
    raise ProbeError(
        f"{fork}: unrecognised MODEXP complexity shape; classify by hand"
    )


def extract(label: str, fork: str, historical: bool = False) -> dict:
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
    requests, requests_source = _requests(fork, historical)
    stack_access, stack_access_source = _stack_access(fork, instructions.Ops)
    complexity, complexity_source = _modexp_complexity(fork, historical)

    def field(path, value, source):
        return (path, {"value": value, "source": source})

    # `createAccess` is the CREATE/CREATE2 base and the creation transaction's
    # recipient cost. Upstream spells it `OPCODE_CREATE_BASE` while the two are
    # the same number, and `CREATE_ACCESS` once EIP-8037 splits the creation
    # transaction's cost apart from the opcode's. Both names are tried, newest
    # first, and the name that answered is recorded. On the historical path a
    # total miss is collected, not raised.
    if hasattr(costs, "CREATE_ACCESS"):
        create_access, create_source = int(costs.CREATE_ACCESS), "vm.gas.GasCosts.CREATE_ACCESS"
    elif not historical:
        create_access = _require_int(costs, "OPCODE_CREATE_BASE", f"{fork}.vm.gas.GasCosts")
        create_source = "vm.gas.GasCosts.OPCODE_CREATE_BASE"
    else:
        create_access, create_source = _hist_cost(
            costs, fork,
            ("OPCODE_CREATE_BASE", "GAS_CREATE", "GAS_CREATE_BASE"),
            "vm.gas.GasCosts")

    if hasattr(costs, "EXECUTION_PER_AUTH_BASE_COST"):
        per_auth = int(costs.EXECUTION_PER_AUTH_BASE_COST)
        per_auth_source = "vm.gas.GasCosts.EXECUTION_PER_AUTH_BASE_COST"
    elif not historical:
        per_auth = _require_int(costs, "AUTH_PER_EMPTY_ACCOUNT", f"{fork}.vm.gas.GasCosts")
        per_auth_source = "vm.gas.GasCosts.AUTH_PER_EMPTY_ACCOUNT"
    else:
        per_auth, per_auth_source = _hist_opt(
            costs, fork, "AUTH_PER_EMPTY_ACCOUNT", "vm.gas.GasCosts")

    # Names that live in different modules at different forks are looked up
    # across every module they are known to inhabit, newest location first.
    if historical:
        blob_target, blob_target_source = _hist_blob(
            costs, fork_module, fork,
            ("BLOB_TARGET_GAS_PER_BLOCK", "TARGET_BLOB_GAS_PER_BLOCK"))
        max_blob_gas, max_blob_gas_source = _hist_blob(
            costs, fork_module, fork, ("MAX_BLOB_GAS_PER_BLOCK",))
        blob_fraction, blob_fraction_source = _hist_blob(
            costs, fork_module, fork, ("BLOB_BASE_FEE_UPDATE_FRACTION",))
    else:
        max_blob_gas, max_blob_gas_source = _require(
            fork, "MAX_BLOB_GAS_PER_BLOCK", ("vm.gas", "fork"))
    if hasattr(costs, "TX_MAX_GAS_LIMIT"):
        tx_max_gas = _require_int(costs, "TX_MAX_GAS_LIMIT", fork)
        tx_max_gas_source = "vm.gas.GasCosts.TX_MAX_GAS_LIMIT"
    else:
        tx_max_gas, tx_max_gas_source = _find(
            fork, "TX_MAX_GAS_LIMIT", ("transactions", "fork"))
    blob_count, blob_count_source = _find(
        fork, "BLOB_COUNT_LIMIT", ("transactions", "fork"))
    max_rlp, max_rlp_source = _find(
        fork, "MAX_RLP_BLOCK_SIZE", ("fork", "transactions"))

    if historical:
        max_init_code, max_init_code_source = _hist_opt(
            interpreter, fork, "MAX_INIT_CODE_SIZE", "vm.interpreter")
        cold_access, cold_access_source = _hist_opt(
            costs, fork, "COLD_ACCOUNT_ACCESS", "vm.gas.GasCosts")
        call_value, call_value_source = _hist_cost(
            costs, fork, ("CALL_VALUE", "GAS_CALLVALUE", "GAS_CALL_VALUE"),
            "vm.gas.GasCosts")
        clear_refund, clear_refund_source = _hist_cost(
            costs, fork, ("REFUND_STORAGE_CLEAR", "REFUND_SCLEAR"),
            "vm.gas.GasCosts")
        access_list_address, access_list_address_source = _hist_opt(
            costs, fork, "TX_ACCESS_LIST_ADDRESS", "vm.gas.GasCosts")
        access_list_key, access_list_key_source = _hist_opt(
            costs, fork, "TX_ACCESS_LIST_STORAGE_KEY", "vm.gas.GasCosts")
        floor_token, floor_token_source = _hist_opt(
            costs, fork, "TX_DATA_TOKEN_FLOOR", "vm.gas.GasCosts")
        entries_head = [
            field("blob.target", blob_target, blob_target_source),
            field("blob.max", max_blob_gas, max_blob_gas_source),
            field("blob.baseFeeUpdateFraction",
                  blob_fraction, blob_fraction_source),
        ]
    else:
        max_init_code, max_init_code_source = (
            _require_int(interpreter, "MAX_INIT_CODE_SIZE", fork),
            "vm.interpreter.MAX_INIT_CODE_SIZE")
        cold_access, cold_access_source = (
            _require_int(costs, "COLD_ACCOUNT_ACCESS", fork),
            "vm.gas.GasCosts.COLD_ACCOUNT_ACCESS")
        call_value, call_value_source = (
            _require_int(costs, "CALL_VALUE", fork),
            "vm.gas.GasCosts.CALL_VALUE")
        clear_refund, clear_refund_source = (
            _require_int(costs, "REFUND_STORAGE_CLEAR", fork),
            "vm.gas.GasCosts.REFUND_STORAGE_CLEAR")
        access_list_address, access_list_address_source = (
            _require_int(costs, "TX_ACCESS_LIST_ADDRESS", fork),
            "vm.gas.GasCosts.TX_ACCESS_LIST_ADDRESS")
        access_list_key, access_list_key_source = (
            _require_int(costs, "TX_ACCESS_LIST_STORAGE_KEY", fork),
            "vm.gas.GasCosts.TX_ACCESS_LIST_STORAGE_KEY")
        floor_token, floor_token_source = (
            _require_int(costs, "TX_DATA_TOKEN_FLOOR", fork),
            "vm.gas.GasCosts.TX_DATA_TOKEN_FLOOR")
        entries_head = [
            field("blob.target", _require_int(costs, "BLOB_TARGET_GAS_PER_BLOCK", fork),
                  "vm.gas.GasCosts.BLOB_TARGET_GAS_PER_BLOCK"),
            field("blob.max", max_blob_gas, max_blob_gas_source),
            field("blob.baseFeeUpdateFraction",
                  _require_int(costs, "BLOB_BASE_FEE_UPDATE_FRACTION", fork),
                  "vm.gas.GasCosts.BLOB_BASE_FEE_UPDATE_FRACTION"),
        ]

    entries = entries_head + [
        field("blob.reserveBaseCost", _opt_int(costs, "BLOB_BASE_COST"),
              "vm.gas.GasCosts.BLOB_BASE_COST (absent before EIP-7918)"),
        field("code.maxCodeSize", _require_int(interpreter, "MAX_CODE_SIZE", fork),
              "vm.interpreter.MAX_CODE_SIZE"),
        field("code.maxInitCodeSize", max_init_code, max_init_code_source),
        field("tx.maxGas", tx_max_gas, tx_max_gas_source),
        field("tx.maxTotalGas", _opt_int(costs, "TX_MAX_TOTAL_GAS_LIMIT"),
              "vm.gas.GasCosts.TX_MAX_TOTAL_GAS_LIMIT (absent before EIP-8037)"),
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
        field("gas.coldAccountAccess", cold_access, cold_access_source),
        field("gas.callValue", call_value, call_value_source),
        field("gas.createAccess", create_access, create_source),
        field("gas.storageClearRefund", clear_refund, clear_refund_source),
        field("gas.txBase", *tx_base_entry(costs, fork, historical)),
        field("gas.txAccessListAddress",
              access_list_address, access_list_address_source),
        field("gas.txAccessListStorageKey",
              access_list_key, access_list_key_source),
        field("gas.floorTokenCost", floor_token, floor_token_source),
        field("gas.perAuthIntrinsic", per_auth, per_auth_source),
        field("gas.codeReadSurcharge", surcharge, surcharge_source),
        field("header.blockAccessListHash", "block_access_list_hash" in header_fields,
              "blocks.Header has a block_access_list_hash field (EIP-7928)"),
        field("header.slotNumber", "slot_number" in header_fields,
              "blocks.Header has a slot_number field (EIP-7843)"),
        field("requests", requests, requests_source),
        field("modexpComplexity", complexity, complexity_source),
    ] + _state_gas(fork) + _bal(fork) + _opcodes(fork, instructions.Ops) \
        + _headers(fork, header_fields) + _access(fork, historical) + _sstore(fork) \
        + _settle(fork, fork_module, historical) + _txr(fork, fork_module, historical) \
        + _creation(fork, interpreter) + _pow(fork, fork_module, historical) \
        + _sys(fork, fork_module) + _bn254(fork, historical)
    seen = [path for path, _ in entries]
    if len(seen) != len(set(seen)):
        raise ProbeError(f"{label}: duplicate field path in the extraction table")
    # D13: the mainnet activation the pinned specification declares for this
    # fork, as a compared row rather than a printed one. `ByTimestamp` carries
    # the timestamp; `Unscheduled` (and any criterion without one) is `None`,
    # which the build's printer answers with `null` while `mainnetChainConfig`
    # names no activation for the fork. The same fact is also kept under
    # `fork_criteria` below for the `--table` report.
    entries.append(field(
        "mainnetActivation",
        criterion_value(criteria),
        f"FORK_CRITERIA ({type(criteria).__name__})",
    ))
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


def schedule() -> dict:
    """Every fork module's mainnet `FORK_CRITERIA`, from Byzantium on."""
    out = {}
    for label, fork in SCHEDULE_FORKS.items():
        criteria = _mod(fork).FORK_CRITERIA
        out[label] = {
            "value": criterion_value(criteria),
            "source": f"ethereum.forks.{fork}.FORK_CRITERIA "
            f"({type(criteria).__name__})",
        }
    return out


def main() -> int:
    if sys.argv[1:] == ["--schedule"]:
        json.dump(schedule(), sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
        return 0
    if sys.argv[1:] == ["--historical"]:
        return emit_historical()
    out = {label: extract(label, fork) for label, fork in FORKS.items()}
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


def emit_historical() -> int:
    """The pre-Prague forks' constants, or a complete miss/error report.

    Every fork is attempted even when an earlier one fails, so one run
    reports the whole repair list: per-fork structural errors plus the
    collected per-field lookup misses. Nothing is emitted while any entry
    is unresolved.
    """
    out = {}
    errors: list[str] = []
    for label, fork in HISTORICAL_FORKS.items():
        try:
            out[label] = extract(label, fork, historical=True)
        except Exception as error:  # noqa: BLE001 -- collected, not hidden
            errors.append(f"{label} ({fork}): {type(error).__name__}: {error}")
    if errors or _MISSES:
        for line in errors:
            print(f"error: {line}", file=sys.stderr)
        if _MISSES:
            print("error: unresolved historical lookups:", file=sys.stderr)
            for line in _MISSES:
                print(f"error:   {line}", file=sys.stderr)
        return 2
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ProbeError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
