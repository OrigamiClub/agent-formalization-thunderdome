import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.

This file states the theorem only.  The single theorem ends in `:= by sorry`; nothing is proved.
-/

namespace ImprovedSunflower

/-- A **sunflower with core `Y`** is a finite family `P` of finsets such that

* every member of `P` contains `Y`, and
* any two *distinct* members of `P` meet in exactly `Y`.

Consequently the *petals* `S \ Y` for `S ∈ P` are pairwise disjoint
(`(S₁ \ Y) ∩ (S₂ \ Y) ⊆ (S₁ ∩ S₂) \ Y = Y \ Y = ∅` when `S₁ ≠ S₂`), and every element
lying in two members of `P` lies in all of them.  The number of petals is `P.card`, and the
members of `P` are automatically distinct because `P` is a `Finset`.

Mathlib has a closely related predicate (as of writing, `Finset.IsSunflower` in
`Mathlib.Combinatorics.SetFamily.Sunflower`, used for the classical Erdős–Ko–Rado bound
`f(k,r) ≤ k! · (r-1)^k`); we give a self-contained definition here to fix the exact shape. -/
def IsSunflower {α : Type*} [DecidableEq α] (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ S ∈ P, Y ⊆ S) ∧ (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every integer `k ≥ 2`, every integer
`r ≥ 1`, and every finite family `W` of finsets each of cardinality exactly `k`, if

`(C · r · log k) ^ k < |W|`

then `W` contains `r` distinct sets forming a sunflower with `r` petals.  Equivalently, the
sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

* `log` is the natural logarithm `Real.log`; changing the logarithm base only rescales `C`.
* The hypothesis `2 ≤ k` is imposed because for `k = 1` one has `log k = 0`, making the bound
  demand only `|W| > 0`, which cannot force `r ≥ 2` petals.  (Statements valid for all positive
  `k` replace `log k` by `log k + 1`, `max (log k) 1`, or `log (k + 1)`; each is absorbed into `C`.)
* `C` is existentially quantified: "there is an absolute constant". -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower Y P := by
  sorry

end ImprovedSunflower
