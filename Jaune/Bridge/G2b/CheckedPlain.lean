import Jaune.Bridge.G2b.CheckedWalk
import Jaune.Bridge.G2b.CheckedDispatch
import Jaune.MessageCall.Plain

namespace Jaune.MemorySimulation

private abbrev PlainSquare (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (op : Jaune.PlainOp) :=
  Square (Checked.Arms.PlainOp.runCore pc ctx s op) (Staging.PlainOp.runCore pc ctx s.toLegacy op)

local macro "plain_square" : tactic => `(tactic| (
  unfold PlainSquare
  simp only [Checked.Arms.PlainOp.runCore, Staging.PlainOp.runCore]
  checked_sq_walk))


private theorem logStep (n : Fin 5) (ctx : CallContext) (m : Checked.Machine) :
    Square (Checked.Arms.PlainOp.logStep n ctx m) (Staging.PlainOp.logStep n ctx m.toLegacy) := by
  unfold Checked.Arms.PlainOp.logStep Staging.PlainOp.logStep
  checked_sq_walk

private theorem liftLog (n : Fin 5) (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.Arms.PlainOp.liftLog (Checked.Arms.PlainOp.logStep n ctx) s)
      (Staging.PlainOp.liftLog (Staging.PlainOp.logStep n ctx) s.toLegacy) := by
  unfold Checked.Arms.PlainOp.liftLog Staging.PlainOp.liftLog
  rw [legacy_stateMachine, (logStep n ctx s.machine).legacy_eq]
  rcases Checked.Arms.PlainOp.logStep n ctx s.machine with ⟨e,m⟩ | ⟨m,l⟩ <;> rfl

private theorem originalStorage_legacy (s : Checked.Frame.State) (orig : State) (a : Address) (key : U256) :
    s.toLegacy.originalStorageValue orig a key = s.originalStorageValue orig a key := rfl

private theorem recordStorageRead_accessedStorageKeys (s : Checked.Frame.State) (r : ForkRules) (a : Address) (k : U256) :
    (s.recordStorageRead r a k).accessedStorageKeys = s.accessedStorageKeys := rfl

private theorem legacy_recordStorageRead_accessedStorageKeys (s : Frame.State) (r : ForkRules) (a : Address) (k : U256) :
    (s.recordStorageRead r a k).accessedStorageKeys = s.accessedStorageKeys := rfl

local macro "storage_align" : tactic => `(tactic| simp only [erase_pair, erase_state, erase_same, legacy_gasLeft,
    legacy_recordStorageRead, legacy_addAccessedStorageKey, legacy_accessedStorageKeys, legacy_withRefund,
    legacy_storageValue, originalStorage_legacy, legacy_refund, legacy_creditStateGasRefund, legacy_setStorageValue,
    legacy_recordAccountRead])

private theorem sstoreBerlin (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.Arms.PlainOp.sstoreBerlin ctx s) (Staging.PlainOp.sstoreBerlin ctx s.toLegacy) := by
  unfold Checked.Arms.PlainOp.sstoreBerlin Staging.PlainOp.sstoreBerlin
  refine Square.bind (Frame.State.pop s) ?_
  rintro ⟨k, t⟩
  refine Square.bind (Frame.State.pop t) ?_
  rintro ⟨v, t⟩
  dsimp only
  simp only [erase_pair, erase_state, erase_same, legacy_gasLeft]
  refine Square.bind (Square.assert _ _) ?_
  intro u
  by_cases h : (ctx.recipient, k) ∈ t.accessedStorageKeys
  · simp only [recordStorageRead_accessedStorageKeys, legacy_recordStorageRead_accessedStorageKeys,
      legacy_accessedStorageKeys, h, not_true_eq_false, ↓reduceIte]
    storage_align
    repeat' first | storage_align | checked_sq_one
  · simp only [recordStorageRead_accessedStorageKeys, legacy_recordStorageRead_accessedStorageKeys,
      legacy_accessedStorageKeys, h, not_false_eq_true, ↓reduceIte]
    storage_align
    repeat' first | storage_align | checked_sq_one

private theorem sstoreLegacy (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.Arms.PlainOp.sstoreLegacy ctx s) (Staging.PlainOp.sstoreLegacy ctx s.toLegacy) := by
  unfold Checked.Arms.PlainOp.sstoreLegacy Staging.PlainOp.sstoreLegacy
  refine Square.bind (Frame.State.pop s) ?_
  rintro ⟨k, t⟩
  refine Square.bind (Frame.State.pop t) ?_
  rintro ⟨v, t⟩
  dsimp only
  simp only [erase_pair, erase_state, erase_same, legacy_gasLeft]
  refine Square.bind (Square.assert _ _) ?_
  intro u
  cases ha : ctx.block.rules.access <;> cases hn : ctx.block.rules.sstore.netMetering
  all_goals
    try
      by_cases h : (ctx.recipient, k) ∈ t.accessedStorageKeys <;>
      simp only [recordStorageRead_accessedStorageKeys, legacy_recordStorageRead_accessedStorageKeys,
        legacy_accessedStorageKeys, h, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  all_goals try storage_align
  all_goals repeat' first | storage_align | checked_sq_one

private theorem sstoreAmsterdam (sg : StateGasRules) (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.Arms.PlainOp.sstoreAmsterdam sg ctx s) (Staging.PlainOp.sstoreAmsterdam sg ctx s.toLegacy) := by
  unfold Checked.Arms.PlainOp.sstoreAmsterdam Staging.PlainOp.sstoreAmsterdam
  refine Square.bind (Frame.State.assertDynamic s ctx) ?_
  intro u
  refine Square.bind (Frame.State.pop s) ?_
  rintro ⟨k, t⟩
  refine Square.bind (Frame.State.pop t) ?_
  rintro ⟨v, t⟩
  try storage_align
  by_cases h : (ctx.recipient, k) ∈ t.accessedStorageKeys
  all_goals simp only [*, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  all_goals repeat' first | storage_align | checked_sq_one

private theorem plain_add (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .add := by plain_square

private theorem plain_mul (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mul := by plain_square

private theorem plain_sub (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sub := by plain_square

private theorem plain_div (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .div := by plain_square

private theorem plain_sdiv (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sdiv := by plain_square

private theorem plain_mod (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mod := by plain_square

private theorem plain_smod (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .smod := by plain_square

private theorem plain_addmod (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .addmod := by plain_square

private theorem plain_mulmod (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mulmod := by plain_square

private theorem plain_exp (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .exp := by plain_square

private theorem plain_signextend (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .signextend := by plain_square

private theorem plain_lt (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .lt := by plain_square

private theorem plain_gt (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .gt := by plain_square

private theorem plain_slt (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .slt := by plain_square

private theorem plain_sgt (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sgt := by plain_square

private theorem plain_eq (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .eq := by plain_square

private theorem plain_iszero (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .iszero := by plain_square

private theorem plain_and (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .and := by plain_square

private theorem plain_or (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .or := by plain_square

private theorem plain_xor (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .xor := by plain_square

private theorem plain_not (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .not := by plain_square

private theorem plain_byte (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .byte := by plain_square

private theorem plain_shl (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .shl := by plain_square

private theorem plain_shr (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .shr := by plain_square

private theorem plain_sar (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sar := by plain_square

private theorem plain_clz (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .clz := by plain_square

private theorem plain_keccak256 (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .keccak256 := by plain_square

private theorem plain_address (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .address := by plain_square

private theorem plain_balance (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .balance := by plain_square

private theorem plain_origin (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .origin := by plain_square

private theorem plain_caller (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .caller := by plain_square

private theorem plain_callvalue (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .callvalue := by plain_square

private theorem plain_calldataload (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .calldataload := by plain_square

private theorem plain_calldatasize (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .calldatasize := by plain_square

private theorem plain_calldatacopy (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .calldatacopy := by plain_square

private theorem plain_codesize (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .codesize := by plain_square

private theorem plain_codecopy (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .codecopy := by plain_square

private theorem plain_gasprice (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .gasprice := by plain_square

private theorem plain_extcodesize (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .extcodesize := by plain_square

private theorem plain_extcodecopy (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .extcodecopy := by plain_square

private theorem plain_returndatasize (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .returndatasize := by plain_square

private theorem plain_returndatacopy (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .returndatacopy := by plain_square

private theorem plain_extcodehash (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .extcodehash := by plain_square

private theorem plain_blockhash (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .blockhash := by plain_square

private theorem plain_coinbase (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .coinbase := by plain_square

private theorem plain_timestamp (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .timestamp := by plain_square

private theorem plain_number (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .number := by plain_square

private theorem plain_prevrandao (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .prevrandao := by plain_square

private theorem plain_gaslimit (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .gaslimit := by plain_square

private theorem plain_chainid (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .chainid := by plain_square

private theorem plain_selfbalance (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .selfbalance := by plain_square

private theorem plain_basefee (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .basefee := by plain_square

private theorem plain_blobhash (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .blobhash := by plain_square

private theorem plain_blobbasefee (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .blobbasefee := by plain_square

private theorem plain_slotnum (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .slotnum := by plain_square

private theorem plain_pop (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .pop := by plain_square

private theorem plain_mload (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mload := by plain_square

private theorem plain_mstore (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mstore := by plain_square

private theorem plain_mstore8 (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mstore8 := by plain_square

private theorem plain_sload (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sload := by plain_square

private theorem plain_sstore (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .sstore := by
  unfold PlainSquare
  simp only [Checked.Arms.PlainOp.runCore, Staging.PlainOp.runCore]
  cases hs : ctx.block.rules.stateGas with
  | some sg => exact sstoreAmsterdam sg ctx s
  | none =>
    rcases h : ctx.block.rules.sstore with ⟨a,b⟩
    cases a <;> cases b <;> cases ctx.block.rules.access <;> first | apply sstoreBerlin | apply sstoreLegacy

private theorem plain_tload (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .tload := by plain_square

private theorem plain_tstore (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .tstore := by plain_square

private theorem plain_mcopy (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .mcopy := by plain_square

private theorem plain_pc (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .pc := by plain_square

private theorem plain_msize (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .msize := by plain_square

private theorem plain_gas (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) :
    PlainSquare pc ctx s .gas := by plain_square

private theorem plain_dup (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (n : Fin 16) :
    PlainSquare pc ctx s (.dup n) := by plain_square

private theorem plain_swap (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (n : Fin 16) :
    PlainSquare pc ctx s (.swap n) := by plain_square

private theorem plain_log (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (n : Fin 5) :
    PlainSquare pc ctx s (.log n) := liftLog n ctx s

private theorem PlainOp.runArms (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (op : Jaune.PlainOp) :
    Square (Checked.Arms.PlainOp.runCore pc ctx s op) (Staging.PlainOp.runCore pc ctx s.toLegacy op) := by
  cases op with
  | add => exact plain_add pc ctx s
  | mul => exact plain_mul pc ctx s
  | sub => exact plain_sub pc ctx s
  | div => exact plain_div pc ctx s
  | sdiv => exact plain_sdiv pc ctx s
  | mod => exact plain_mod pc ctx s
  | smod => exact plain_smod pc ctx s
  | addmod => exact plain_addmod pc ctx s
  | mulmod => exact plain_mulmod pc ctx s
  | exp => exact plain_exp pc ctx s
  | signextend => exact plain_signextend pc ctx s
  | lt => exact plain_lt pc ctx s
  | gt => exact plain_gt pc ctx s
  | slt => exact plain_slt pc ctx s
  | sgt => exact plain_sgt pc ctx s
  | eq => exact plain_eq pc ctx s
  | iszero => exact plain_iszero pc ctx s
  | and => exact plain_and pc ctx s
  | or => exact plain_or pc ctx s
  | xor => exact plain_xor pc ctx s
  | not => exact plain_not pc ctx s
  | byte => exact plain_byte pc ctx s
  | shl => exact plain_shl pc ctx s
  | shr => exact plain_shr pc ctx s
  | sar => exact plain_sar pc ctx s
  | clz => exact plain_clz pc ctx s
  | keccak256 => exact plain_keccak256 pc ctx s
  | address => exact plain_address pc ctx s
  | balance => exact plain_balance pc ctx s
  | origin => exact plain_origin pc ctx s
  | caller => exact plain_caller pc ctx s
  | callvalue => exact plain_callvalue pc ctx s
  | calldataload => exact plain_calldataload pc ctx s
  | calldatasize => exact plain_calldatasize pc ctx s
  | calldatacopy => exact plain_calldatacopy pc ctx s
  | codesize => exact plain_codesize pc ctx s
  | codecopy => exact plain_codecopy pc ctx s
  | gasprice => exact plain_gasprice pc ctx s
  | extcodesize => exact plain_extcodesize pc ctx s
  | extcodecopy => exact plain_extcodecopy pc ctx s
  | returndatasize => exact plain_returndatasize pc ctx s
  | returndatacopy => exact plain_returndatacopy pc ctx s
  | extcodehash => exact plain_extcodehash pc ctx s
  | blockhash => exact plain_blockhash pc ctx s
  | coinbase => exact plain_coinbase pc ctx s
  | timestamp => exact plain_timestamp pc ctx s
  | number => exact plain_number pc ctx s
  | prevrandao => exact plain_prevrandao pc ctx s
  | gaslimit => exact plain_gaslimit pc ctx s
  | chainid => exact plain_chainid pc ctx s
  | selfbalance => exact plain_selfbalance pc ctx s
  | basefee => exact plain_basefee pc ctx s
  | blobhash => exact plain_blobhash pc ctx s
  | blobbasefee => exact plain_blobbasefee pc ctx s
  | slotnum => exact plain_slotnum pc ctx s
  | pop => exact plain_pop pc ctx s
  | mload => exact plain_mload pc ctx s
  | mstore => exact plain_mstore pc ctx s
  | mstore8 => exact plain_mstore8 pc ctx s
  | sload => exact plain_sload pc ctx s
  | sstore => exact plain_sstore pc ctx s
  | tload => exact plain_tload pc ctx s
  | tstore => exact plain_tstore pc ctx s
  | mcopy => exact plain_mcopy pc ctx s
  | pc => exact plain_pc pc ctx s
  | msize => exact plain_msize pc ctx s
  | gas => exact plain_gas pc ctx s
  | dup n => exact plain_dup pc ctx s n
  | swap n => exact plain_swap pc ctx s n
  | log n => exact plain_log pc ctx s n

/-- The checked plain instructions against the staged ones, composed through the family dispatch's
bridge (`Checked.PlainOp.runCore_arms`) and the per-opcode squares above. -/
theorem PlainOp.runCore (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (op : Jaune.PlainOp) :
    Square (Checked.PlainOp.runCore pc ctx s op) (Staging.PlainOp.runCore pc ctx s.toLegacy op) := by
  rw [Checked.PlainOp.runCore_arms]
  exact PlainOp.runArms pc ctx s op

end Jaune.MemorySimulation
