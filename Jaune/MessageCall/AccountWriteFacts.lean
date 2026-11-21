import Jaune.MessageCall.State
import Jaune.AccountWriteFacts

/-!
# Account protection through the checked beneficiary credit (goal `jaune-shape-and-names-v1`, G2b)

`SELFDESTRUCT`'s beneficiary credit over the checked frame state (`Frame.State.creditBeneficiary`)
keeps a protected account protected and leaves its storage alone. These are the W6b protection
facts that were stated over the waiting `Devm.creditBeneficiary`, restated with the same
premises and conclusions over `Frame.State`.
-/

namespace Jaune

open Jaune

/-- The beneficiary credit keeps a protected account protected. -/
theorem State.Protected.creditBeneficiary {s : Frame.State} {a : Address}
    (hp : s.world.state.Protected a) (rules : ForkRules) (donee : Address) (value : U256) :
    (s.creditBeneficiary rules donee value).world.state.Protected a := by
  unfold Frame.State.creditBeneficiary
  split
  · exact hp.setBalance donee _
  · change (s.world.state.setPresent donee _).Protected a
    unfold Jaune.State.Protected at hp ⊢
    by_cases same : donee = a
    · subst a
      rw [Jaune.State.get_setPresent_self]
      exact hp
    · rw [Jaune.State.get_setPresent_ne _ same]
      exact hp

/-- The beneficiary credit leaves a protected account's storage unchanged. -/
theorem Frame.State.creditBeneficiary_storage_of_protected (rules : ForkRules) (donee : Address)
    (value : U256) (s : Frame.State) (a : Address) (hp : s.world.state.Protected a) :
    ((s.creditBeneficiary rules donee value).world.state.get a).storage =
      (s.world.state.get a).storage := by
  unfold Frame.State.creditBeneficiary
  split
  · exact Jaune.State.setBalance_storage_of_protected hp
  · change ((s.world.state.setPresent donee
      ((s.world.state.get donee).withBalance (s.world.state.balance donee + value))).get a).storage =
        (s.world.state.get a).storage
    by_cases same : donee = a
    · subst a
      rw [Jaune.State.get_setPresent_self]
      rfl
    · rw [Jaune.State.get_setPresent_ne _ same]

end Jaune
