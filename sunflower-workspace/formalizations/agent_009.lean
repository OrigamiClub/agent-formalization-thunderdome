/-
  Agent 009 — Independent formalization diversity study
  Statement (only) of the improved sunflower lemma.

  Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
  Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
  positive integers `k` and `r`, every finite family `W` of `k`-element sets with
  `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.
-/

import Mathlib

namespace ImprovedSunflower

/-- A finite family of finsets `P` forms a **sunflower with core `Y`** if any two
distinct members of `P` meet in exactly `Y`.  Equivalently, the "petals" `A \ Y`
for `A ∈ P` are pairwise disjoint.  The number of *petals* is `P.card`.

This mirrors Mathlib's sunflower predicate in
`Mathlib/Combinatorics/SetFamily/Sunflower.lean` (there stated, up to naming, as
`(𝒮 : Set (Finset α)).Pairwise fun s₁ s₂ => s₁ ∩ s₂ = t`); it is reproduced here
so that the file is self-contained and independent of the exact Mathlib
signature. -/
def IsSunflower {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  (P : Set (Finset α)).Pairwise fun A B => A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that the following holds.  Let `k` and
`r` be positive integers with `k ≥ 2` (so `Real.log k > 0`; the cases `k ≤ 1` are
degenerate, see the companion note).  Let `W` be a finite family of finsets over an
ambient type `α`, each of cardinality exactly `k`.  If
`|W| > (C · r · log k)^k`, then `W` contains a **sunflower with `r` petals**: a
subfamily `P ⊆ W` consisting of exactly `r` sets that share a common core `Y`
(so the `r` sets are pairwise distinct and all pairwise intersections equal `Y`).

Equivalently, writing `f(k, r)` for the sunflower function (the least `N` such that
every family of `N` sets of size `k` contains an `r`-petal sunflower), one has
`f(k, r) ≤ (C · r · log k)^k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ A ∈ W, A.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y := by
  sorry

/-- Restatement in terms of an explicitly supplied constant `C` (a hypothesis
`hC : C ≥ C₀` is folded into "there exists `C`" in `improved_sunflower_lemma`;
this version is convenient when the constant is treated as fixed input data). -/
theorem improved_sunflower_lemma_const
    (C : ℝ) (hC : 0 < C)
    (hbig : ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      2 ≤ k → 1 ≤ r → (∀ A ∈ W, A.card = k) →
      (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
      ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y) :
    True := by
  sorry

end ImprovedSunflower
