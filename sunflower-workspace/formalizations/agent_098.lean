import Mathlib

/-!
# Improved sunflower lemma — statement only

Alweiss–Lovett–Wu–Zhang (2019), with the refinements of Rao and of
Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace Agent098

/-- A finite family `𝒮` of finite sets is a **sunflower with core `Y`** when every
two distinct members meet in exactly `Y`.

This "all pairwise intersections coincide" formulation is equivalent to the usual
description: every element lying in at least two members of `𝒮` lies in all of
them, and the petals `S \ Y` (for `S ∈ 𝒮`) are pairwise disjoint.  The number of
**petals** is `𝒮.card`.  Note that if `𝒮` has at least two members then `Y` is
uniquely determined, and distinctness of the members forces every petal to be
nonempty. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**
There is an absolute constant `C` such that for every ambient type `α`, every
`k ≥ 2`, every `r ≥ 1`, and every finite family `W` of sets each of cardinality
exactly `k`, if
`|W| > (C * r * Real.log k) ^ k`
then `W` contains a sunflower with `r` petals: a subfamily `𝒮 ⊆ W` of exactly `r`
sets which all share a common pairwise intersection `Y` (the core).

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`.

The constant `C` is quantified once, outside the quantifier over `α`, `k`, `r`,
`W`, so it is genuinely absolute.  The natural logarithm `Real.log` is used; the
choice of base is irrelevant since it is absorbed into `C`.  The hypothesis
`2 ≤ k` avoids the degenerate case `Real.log 1 = 0`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ) →
        ∃ 𝒮 ⊆ W, ∃ Y : Finset α, 𝒮.card = r ∧ IsSunflower 𝒮 Y := by
  sorry

end Agent098
