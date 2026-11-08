import Jaune.Transaction
import JauneConsensus.Config

/-!
# One fork notion across the two layers (outcome O7)

The consensus layer's fork axis, `CFork`, and its pairing with Jaune's execution-layer `Fork`
(`Jaune/Fork.lean`). The consensus layer imports the execution layer, never the reverse, so both
directions of the pairing live here.

| consensus (`specs/<fork>/`) | execution (`Jaune.Fork`) | status here |
|---|---|---|
| `deneb` | `cancun` | pre-fork side only (Electra `fork` and `transition` vectors) |
| `electra` | `prague` | implemented by this goal |
| `fulu` | `osaka`, `bpo1`, `bpo2` | implemented by this goal |
| `gloas` | `amsterdam` | declared, **refused**: no rule data resolves |

BPO1 and BPO2 are not consensus forks. On the consensus side they are the two entries of Fulu's
`BLOB_SCHEDULE` (`configs/mainnet.yaml` at `v1.6.1`, generated into `Config.mainnet`: epoch
412672, 15 blobs; epoch 419072, 21 blobs), read by `get_blob_parameters`; on the execution side they are the `bpo1` and `bpo2`
rule sets, which differ from Osaka only in their blob schedule. Before the first entry Fulu uses
`MAX_BLOBS_PER_BLOCK_ELECTRA` (9), which is Osaka's ceiling.

`CFork.rules?` is the single resolver, as `Fork.rules?` is on the execution side. Gloas
resolves to `none`, so every consumer refuses it by name; nothing falls back to Fulu. The
`v1.6.1` vector tree also ships an `eip7805` feature-fork directory; it has no `CFork` value and
`CFork.resolve` refuses it, and every other unknown name, the same way.

Ties checked here by `decide` (each fails to elaborate if either side's data moves):

* the pairing and its inverse agree (`CFork.mem_executionForks_iff`);
* each execution fork's blob-gas ceiling is the consensus layer's blob count times
  `GAS_PER_BLOB = 2^17` (`CForkData.blobs_tie`);
* the request types: consensus `WITHDRAWAL_REQUEST_TYPE` and `CONSOLIDATION_REQUEST_TYPE` are
  exactly the system-contract request types in the execution rule data, in order, and
  `DEPOSIT_REQUEST_TYPE` is Jaune's receipt-derived `depositRequestType`
  (`CForkData.requestTypes_tie`);
* `get_execution_requests_list` (`specs/electra/beacon-chain.md`) returns `Sequence[bytes]`,
  modelled as `ExecutionRequestsList := List Bytes`, which is definitionally the input type of
  Jaune's `computeRequestsHash` (EIP-7685), so a later seam goal can state their equality with no
  conversion.
-/

namespace JauneConsensus

open Jaune

/-- The consensus-layer forks this goal knows. Deneb exists only as Electra's pre-fork side;
Gloas is declared and refused. -/
inductive CFork where
  | deneb
  | electra
  | fulu
  | gloas
  deriving DecidableEq, Repr, Inhabited

namespace CFork

def all : List CFork := [.deneb, .electra, .fulu, .gloas]

/-- The fork directory name used by the specs and the vector tree. -/
def name : CFork → String
  | .deneb => "deneb"
  | .electra => "electra"
  | .fulu => "fulu"
  | .gloas => "gloas"

instance : ToString CFork := ⟨name⟩

/-- Strict name parsing: no case folding, no fallback. -/
def ofName? : String → Option CFork
  | "deneb" => some .deneb
  | "electra" => some .electra
  | "fulu" => some .fulu
  | "gloas" => some .gloas
  | _ => none

def ord : CFork → Nat
  | .deneb => 0
  | .electra => 1
  | .fulu => 2
  | .gloas => 3

/-- `f.atLeast g`: `f` is `g` or later (the gate for fork-introduced fields). -/
def atLeast (f g : CFork) : Bool := g.ord ≤ f.ord

/-- The execution-layer forks each consensus fork pairs with. -/
def executionForks : CFork → List Fork
  | .deneb => [.cancun]
  | .electra => [.prague]
  | .fulu => [.osaka, .bpo1, .bpo2]
  | .gloas => [.amsterdam]

end CFork

/-- The inverse pairing: total, `none` before Cancun. -/
def _root_.Jaune.Fork.consensusFork? : Fork → Option CFork
  | .cancun => some .deneb
  | .prague => some .electra
  | .osaka | .bpo1 | .bpo2 => some .fulu
  | .amsterdam => some .gloas
  | _ => none

theorem CFork.ofName?_name (c : CFork) : CFork.ofName? c.name = some c := by
  cases c <;> rfl

theorem CFork.mem_executionForks_iff (c : CFork) (f : Fork) :
    f ∈ c.executionForks ↔ f.consensusFork? = some c := by
  cases c <;> cases f <;> decide

/-- `GAS_PER_BLOB` (EIP-4844): the execution layer's `BlobSchedule` counts gas, the consensus
layer counts blobs. -/
def gasPerBlob : Nat := 2 ^ 17

/-- `DEPOSIT_REQUEST_TYPE`, `WITHDRAWAL_REQUEST_TYPE`, `CONSOLIDATION_REQUEST_TYPE`
(`specs/electra/beacon-chain.md`, "Execution layer triggered requests"). -/
def depositRequestType : UInt8 := 0x00
def withdrawalRequestType : UInt8 := 0x01
def consolidationRequestType : UInt8 := 0x02

/-- `get_execution_requests_list`'s result type, `Sequence[bytes]`: each entry is a request type
byte followed by the SSZ serialization of that type's list. -/
abbrev ExecutionRequestsList : Type := List Bytes

/-- The consensus request list feeds Jaune's EIP-7685 commitment with no conversion. -/
def ExecutionRequestsList.requestsHash (l : ExecutionRequestsList) : B256 :=
  computeRequestsHash l

/-- What a resolved consensus fork carries for the cross-layer ties. -/
structure CForkData where
  fork : CFork
  /-- Each paired execution fork with the consensus layer's maximum blobs per block while it is
  active (`MAX_BLOBS_PER_BLOCK`, `MAX_BLOBS_PER_BLOCK_ELECTRA`, or a `BLOB_SCHEDULE` entry of
  `configs/mainnet.yaml`). -/
  blobs : List (Fork × Nat)
  /-- The execution request types the fork's `process_operations` consumes, in
  `get_execution_requests_list` order. -/
  requestTypes : List UInt8
  deriving Repr

-- The blob counts are read from the generated mainnet configuration (`Config.mainnet`, from
-- `configs/mainnet.yaml`), so the ties below follow the pinned config, not a restatement.

def denebData : CForkData :=
  -- `MAX_BLOBS_PER_BLOCK`; Deneb has no execution requests.
  { fork := .deneb, blobs := [(.cancun, Config.mainnet.MAX_BLOBS_PER_BLOCK)], requestTypes := [] }

def electraData : CForkData :=
  { fork := .electra, blobs := [(.prague, Config.mainnet.MAX_BLOBS_PER_BLOCK_ELECTRA)],
    requestTypes := [depositRequestType, withdrawalRequestType, consolidationRequestType] }

def fuluData : CForkData :=
  -- `get_blob_parameters`: Electra's count before the first `BLOB_SCHEDULE` entry, then each
  -- entry in turn; the mainnet schedule's two entries are BPO1 and BPO2.
  { fork := .fulu,
    blobs := (.osaka, Config.mainnet.MAX_BLOBS_PER_BLOCK_ELECTRA) ::
      [Fork.bpo1, Fork.bpo2].zip (Config.mainnet.BLOB_SCHEDULE.map (·.MAX_BLOBS_PER_BLOCK)),
    requestTypes := [depositRequestType, withdrawalRequestType, consolidationRequestType] }

/-- The single resolver. Gloas is declared and refused: `none`. -/
def CFork.rules? : CFork → Option CForkData
  | .deneb => some denebData
  | .electra => some electraData
  | .fulu => some fuluData
  | .gloas => none

/-- Why a fork name is refused for a run. -/
inductive ForkRefusal where
  /-- Not a consensus fork this goal implements (for example `eip7805` or a typo). -/
  | unknown (name : String)
  /-- A declared fork whose rules do not resolve (Gloas). -/
  | unimplemented (fork : CFork)

def ForkRefusal.render : ForkRefusal → String
  | .unknown n => s!"refused: {n} is not a consensus fork this goal implements"
  | .unimplemented c =>
    s!"refused: {c.name} is declared (paired with {c.executionForks}) but not implemented; it fails closed"

instance : ToString ForkRefusal := ⟨ForkRefusal.render⟩

/-- Resolve a fork name for a run: the name must be a `CFork` whose rules resolve. Gloas, the
`eip7805` feature fork and every unknown name are refused; nothing is ever run as Fulu. -/
def CFork.resolve (n : String) : Except ForkRefusal CForkData :=
  match CFork.ofName? n with
  | none => .error (.unknown n)
  | some c =>
    match c.rules? with
    | some d => .ok d
    | none => .error (.unimplemented c)

theorem CFork.rules?_fork (c : CFork) (d : CForkData) (h : c.rules? = some d) : d.fork = c := by
  cases c <;> simp [CFork.rules?] at h <;> subst h <;> rfl

theorem CFork.rules?_gloas : CFork.gloas.rules? = none := rfl

/-- The blob list of a resolved fork names exactly its paired execution forks. -/
theorem CForkData.blobs_forks (c : CFork) (d : CForkData) (h : c.rules? = some d) :
    d.blobs.map (·.1) = c.executionForks := by
  cases c <;> simp [CFork.rules?] at h <;> subst h <;> rfl

/-- Blob tie: each paired execution fork's `MAX_BLOB_GAS_PER_BLOCK` (Jaune's rule data) is the
consensus maximum blob count times `GAS_PER_BLOB`. -/
theorem CForkData.blobs_tie (c : CFork) (d : CForkData) (h : c.rules? = some d) :
    ∀ p ∈ d.blobs, p.1.ruleSet.blob.max = p.2 * gasPerBlob := by
  cases c <;> simp [CFork.rules?] at h <;> subst h <;> decide

/-- Request-type tie: the non-deposit request types are exactly the system-contract request
types of every paired execution rule set, in order, and the deposit type is Jaune's
receipt-derived `depositRequestType`. -/
theorem CForkData.requestTypes_tie (c : CFork) (d : CForkData) (h : c.rules? = some d)
    (hne : d.requestTypes ≠ []) :
    d.requestTypes.head? = some depositRequestType ∧
    [depositRequestType] = Jaune.depositRequestType ∧
    ∀ f ∈ c.executionForks, f.ruleSet.requests.map (·.1) = d.requestTypes.tail := by
  cases c <;> simp [CFork.rules?] at h <;> subst h
  · exact absurd rfl hne
  all_goals exact ⟨rfl, rfl, by decide⟩

/-! ## The pairing, rendered (`lake exe jaune-consensus --forks`) -/

def CFork.statusText : CFork → String
  | .deneb => "pre-fork side (Electra fork/transition vectors)"
  | .electra | .fulu => "implemented by this goal"
  | .gloas => "REFUSED: declared, not implemented (fails closed)"

/-- One line per (consensus fork, execution fork) pair. -/
def pairingTable : List String :=
  let header := "consensus  execution  max-blobs  exec-max-blob-gas  request-types  status"
  header :: CFork.all.flatMap fun c =>
    c.executionForks.map fun f =>
      let blobs : String := match c.rules? with
        | some d => match (d.blobs.find? (·.1 == f)) with
          | some (_, n) => toString n
          | none => "-"
        | none => "-"
      let reqs : String := match c.rules? with
        | some d => if d.requestTypes.isEmpty then "none" else toString (d.requestTypes.map (·.toNat))
        | none => "-"
      s!"{c.name}  {f}  {blobs}  {f.ruleSet.blob.max}  {reqs}  {c.statusText}"

#guard (CFork.resolve "gloas").toBool == false
#guard (CFork.resolve "eip7805").toBool == false
#guard (CFork.resolve "Fulu").toBool == false
#guard ((CFork.resolve "fulu").toOption.map (·.fork)) == some .fulu

end JauneConsensus
