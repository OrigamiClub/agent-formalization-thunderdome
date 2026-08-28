import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*. The theorem is closed with `sorry`.
-/

namespace ImprovedSunflowerLemma

/-- `IsSunflower P Y` states that the finsets in `P` form a **sunflower with core `Y`**:
any two distinct members of `P` intersect in exactly `Y`.

The *petals* are the sets `S \ Y` for `S ∈ P`. For two distinct members `S₁ ≠ S₂`
the petals are disjoint, since `S₁ ∩ S₂ = Y`. Every point lying in at least two
members lies in `Y`, hence in all members that contain it as part of a pairwise
intersection. -/
def IsSunflower {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S₁⦄, S₁ ∈ P → ∀ ⦃S₂⦄, S₂ ∈ P → S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- `HasSunflowerOfSize W r` states that the family `W` **contains a sunflower with `r`
petals**: some subfamily `P ⊆ W` of exactly `r` (necessarily distinct) finsets is a
sunflower for some core `Y`. -/
def HasSunflowerOfSize {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ P ⊆ W, P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for every `k ≥ 2`, every `r ≥ 1`,
and every finite family `W` of finsets each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Notes on the encoding:
* `C` is existentially quantified together with its positivity.
* The ambient type `α` is quantified *inside* the existential, so `C` is genuinely
  absolute (independent of the ground set).
* `Real.log` is the natural logarithm; the choice of base only rescales `C`.
* The hypothesis `2 ≤ k` avoids the degenerate case `k = 1`, where `log k = 0`
  makes the right-hand side `0`; for `k = 1` any `r` distinct singletons already
  form a sunflower with empty core, so nothing is lost.
* The comparison `... < (W.card : ℝ)` casts the natural-number cardinality to `ℝ`.
* Distinctness of the `r` sunflower members is automatic from `Finset`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            HasSunflowerOfSize W r := by
  sorry

end ImprovedSunflowerLemma
