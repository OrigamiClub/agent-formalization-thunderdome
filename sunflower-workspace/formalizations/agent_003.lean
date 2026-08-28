/-
  Agent 003 — Independent formalization of the *statement* of the
  improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
  Bell–Chueluecha–Warnke).

  Statement only.  Every theorem ends in `:= by sorry`; nothing is proved.

  Encoding summary (see agent_003.md for rationale):
  * A set family is `W : Finset (Finset α)` over an ambient type `α` with
    `[DecidableEq α]`.  Membership of `Finset` already forces the members to be
    pairwise distinct, so no separate distinctness hypothesis is needed.
  * `IsSunflowerCore 𝒮 Y`  :  every two distinct members of `𝒮` meet exactly in
    `Y`, and `Y` is contained in every member (the latter is automatic once
    `𝒮` has ≥ 2 members but is stated so the predicate behaves for small `𝒮`).
  * `HasSunflower W r`  :  `W` has an `r`-element subfamily that is a sunflower
    (for some core).  `r` petals ↔ subfamily of cardinality `r`.
  * Logarithm: `Real.log` (natural log).  The statement is restricted to `2 ≤ k`
    so that `Real.log k > 0`; for `k = 1` the factor `log k = 0` would make the
    bound vacuously demand a sunflower in every one-set-per-singleton family,
    which is a genuine (if trivial) separate case.  `1 ≤ r`.
  * The absolute constant `C` is existentially quantified as the outermost
    binder, so a single `C` works uniformly for every `α`, `k`, `r`, `W`.
  * Cardinalities via `Finset.card`; the size comparison `|W| > (C r log k)^k`
    is stated in `ℝ` after coercing `W.card`.
-/
import Mathlib

open scoped BigOperators

namespace ImprovedSunflower

variable {α : Type*}

/-- `IsSunflowerCore 𝒮 Y` : the finite family `𝒮` of finsets is a *sunflower with
core `Y`* — any two distinct members intersect exactly in `Y`, and `Y` lies
inside every member.  The "petals" are the sets `S \ Y` for `S ∈ 𝒮`; the
conditions below force them to be pairwise disjoint and to have `Y` removed
cleanly. -/
def IsSunflowerCore [DecidableEq α] (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ S ∈ 𝒮, Y ⊆ S) ∧
    ∀ ⦃S₁ : Finset α⦄, S₁ ∈ 𝒮 → ∀ ⦃S₂ : Finset α⦄, S₂ ∈ 𝒮 → S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- `HasSunflower W r` : the family `W` contains a sunflower with `r` petals,
i.e. an `r`-element subfamily `𝒮 ⊆ W` that is a sunflower for some core `Y`. -/
def HasSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ Y : Finset α, IsSunflowerCore 𝒮 Y

/-- **Improved sunflower lemma.**  There is an absolute constant `C` such that,
for every ambient type `α`, all integers `k ≥ 2` and `r ≥ 1`, and every finite
family `W` of `k`-element finsets over `α`, if `|W| > (C · r · log k)^k` then `W`
contains a sunflower with `r` petals.  Equivalently, the sunflower function
satisfies `f(k, r) ≤ (C · r · log k)^k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

/-- Restatement in terms of a "sunflower function" `f`.  If `f k r` is the least
size such that *every* family of `f k r` many `k`-element finsets contains an
`r`-petal sunflower (encoded here abstractly by the hypothesis `hf`), then `f`
is bounded by `(C · r · log k)^k`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
      ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) → f k r ≤ W.card →
        HasSunflower W r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k r : ℕ, 2 ≤ k → 1 ≤ r → (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
