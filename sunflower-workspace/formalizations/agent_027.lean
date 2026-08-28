import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace Agent027

variable {α : Type*} [DecidableEq α]

/-- A family `P` of finite subsets of `α` is a *sunflower with `r` petals* and
*core* `Y` when `P` has exactly `r` members (which are then automatically
pairwise distinct, `P` being a `Finset`) and any two distinct members of `P`
intersect in exactly `Y`.

Consequences of this definition when `r ≥ 2`: `Y ⊆ s` for every `s ∈ P`; the
petals `s \ Y` for `s ∈ P` are pairwise disjoint; and every element of `α`
contained in at least two members of `P` is contained in all of them. -/
def IsSunflower (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang, 2019; refined by Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every pair of positive
integers `k`, `r` and every finite family `W` of sets, each of cardinality
exactly `k`, if `|W| > (C · r · log (k + 1)) ^ k` then `W` contains a sunflower
with `r` petals.

Encoding notes (see the accompanying `.md`):
* Sets are `Finset α` over an arbitrary ambient type `α`; the family is
  `W : Finset (Finset α)`, whose members are automatically distinct.
* `C` is existentially quantified *outside* the quantifiers over `α`, `k`, `r`,
  `W`, so it is a genuinely absolute constant.
* `Real.log ((k : ℝ) + 1)` is used in place of `Real.log k`: the two agree up to
  a constant factor (absorbed into `C`), and this keeps the bound meaningful and
  the statement true at the boundary `k = 1`, where `Real.log 1 = 0`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type u} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end Agent027
