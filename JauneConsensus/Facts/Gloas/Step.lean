import JauneConsensus.Facts.AnchorInv
import JauneConsensus.GloasEpoch

/-!
# A relation-parametric step generator for Gloas states (goal `eip8282-gloas-cross-layer-v1`, U3)

`Facts/AnchorInv.lean` proves that each Electra/Fulu step preserves one relation, `Pres`, with a
verification-condition generator (`vcg_step`) whose leaf rules name `Pres`. The Gloas state is a
separate structure, and the Gloas preservation rows (B1 to B7) need several relations (a frame
over the builder fields, credential and queue relations, ...). This module lifts the generator
over the relation: a `StepRel σ` is any reflexive and transitive relation on states, and the
tactic `gstep` discharges `Ok c (fun r => rel.R s (f r))` for a `do` block `c` by walking its
binds, conditionals and loops, closing each leaf through two extensible hooks:

* `gstep_close` proves `rel.R s s'` where `s'` is built from `s` by record updates (default:
  `rel.refl`; each relation adds its own rule, e.g. `⟨rfl, rfl, rfl⟩` for a frame);
* `gstep_rebase h` (default: `StepRel.ok_rebase` with the relation inferred) moves the goal onto
  the state a sub-step produced;
* `gstep_of h` proves `rel.R s (f x)` from `h : c' = .ok x` for a sub-step `c'` whose relation
  lemma is already proved (each relation registers its lemmas by `macro_rules`, as
  `AnchorInv.lean` does for `pres_of`, in the form
  `(have hh := StepRel.of_ok (lemma _ ..) $h; exact hh)`, so that the lemma's result type, possibly
  through a projection such as `p.1`, is fixed before it meets the goal); the loop rules (`ok_forIn_list`, `ok_forIn_array`) are
  registered once here for every relation.

It imports `AnchorInv`'s generic combinators (`Ok`, `ok_bind`, `ok_ite`, `ok_dite`, `ok_pure`,
`ok_throw`, `ok_throw_bind`, `bind_eq_ok_iff`, `list_forIn_rel`, `array_forIn_rel`) and does not
edit them.
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

/-- A step relation on states: reflexive and transitive. -/
structure StepRel (σ : Type) where
  R : σ → σ → Prop
  refl : ∀ s, R s s
  trans : ∀ {a b c}, R a b → R b c → R a c

namespace StepRel

variable {σ : Type} (rel : StepRel σ)

/-- Rebase: if every result of `c` is related (through `f`) to `s₁`, and `s₁` is related to `s`,
every result is related to `s`. -/
theorem ok_rebase {α : Type} {s s₁ : σ} {c : M α} {f : α → σ} (h₁ : rel.R s s₁)
    (h : Ok c (fun r => rel.R s₁ (f r))) : Ok c (fun r => rel.R s (f r)) :=
  fun a ha => rel.trans h₁ (h a ha)

/-- A `for` loop over a list whose body relates its state (through `proj`) to the next one
relates the initial state to the final one. -/
theorem ok_forIn_list {α β : Type} (proj : β → σ) {xs : List α} {init : β}
    {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => rel.R (proj b) (proj r.value))) :
    Ok (forIn xs init body) (fun out => rel.R (proj init) (proj out)) :=
  fun out h => list_forIn_rel (fun a b => rel.R (proj a) (proj b)) (fun _ => rel.refl _)
    (fun _ _ _ h₁ h₂ => rel.trans h₁ h₂) body (fun a b r hr => hb a b r hr) xs init out h

/-- The array form of `ok_forIn_list`. -/
theorem ok_forIn_array {α β : Type} (proj : β → σ) {xs : Array α} {init : β}
    {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Ok (body a b) (fun r => rel.R (proj b) (proj r.value))) :
    Ok (forIn xs init body) (fun out => rel.R (proj init) (proj out)) :=
  fun out h => array_forIn_rel (fun a b => rel.R (proj a) (proj b)) (fun _ => rel.refl _)
    (fun _ _ _ h₁ h₂ => rel.trans h₁ h₂) body (fun a b r hr => hb a b r hr) xs init out h

/-- The relation lemma of a sub-step, in the form `gstep_of` consumes. -/
theorem of_ok {α : Type} {c : M α} {Q : α → Prop} {x : α} (h : Ok c Q) (hx : c = .ok x) : Q x :=
  h x hx

end StepRel

/-- Close `rel.R s s'` at a `pure`. Extensible by `macro_rules`. -/
syntax "gstep_close" : tactic
macro_rules | `(tactic| gstep_close) => `(tactic| exact StepRel.refl _ _)

/-- Prove `rel.R s (f x)` from `h : c = .ok x`. Extensible by `macro_rules`. -/
syntax "gstep_of " term : tactic

/-- Rebase the goal `Ok c (fun r => rel.R s (f r))` on the state `x` of `h : c' = .ok x`, through
`gstep_of h`. Extensible by `macro_rules`: a relation whose `R` the generator's `dsimp` unfolds
registers a rule naming its `StepRel` explicitly. -/
syntax "gstep_rebase " term : tactic
macro_rules | `(tactic| gstep_rebase $h) => `(tactic| refine StepRel.ok_rebase _ (by gstep_of $h) ?_)

/-- One generator step on a goal `Ok c Q`. -/
syntax "gstep" : tactic

/-- The generator: `gstep` to a fixed point. -/
macro "gvcg" : tactic => `(tactic| repeat' gstep)

macro_rules | `(tactic| gstep) => `(tactic| first
  | with_reducible exact ok_throw
  | with_reducible exact ok_throw_bind
  | (with_reducible apply ok_pure; gstep_close)
  | (with_reducible apply ok_bind; intro _ hx
     first | gstep_rebase hx | skip)
  | (with_reducible apply ok_ite <;> intro _)
  | (with_reducible apply ok_dite <;> intro _)
  | (set_option simprocs false in dsimp only)
  | (rename_i x _; is_small_inductive x; cases x; all_goals (set_option simprocs false in dsimp only))
  | split)

/-- Loops: the loop state is the step's state (`proj = id`). -/
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.of_ok (StepRel.ok_forIn_list _ id ?_) $h; intro _ _; gvcg))
macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.of_ok (StepRel.ok_forIn_array _ id ?_) $h; intro _ _; gvcg))

end JauneConsensus.Facts.Gloas
