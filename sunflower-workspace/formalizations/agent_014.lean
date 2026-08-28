import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*; the proof is `sorry`.
-/

namespace Agent014

/-- A **sunflower with `r` petals** and **core** `Y`: a family `P` of exactly `r`
sets (they are automatically distinct, being the elements of a `Finset`) whose
pairwise intersections are all equal to `Y`.

The petals are the sets `S \ Y` for `S ∈ P`; the definition is equivalent to
saying the petals are pairwise disjoint, and that every element lying in at least
two members of `P` lies in `Y` (hence in every member). -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃S₁⦄, S₁ ∈ P → ∀ ⦃S₂⦄, S₂ ∈ P → S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every `k ≥ 2` and every
`r ≥ 1`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals (some subfamily
`P ⊆ W` that is a sunflower with `r` petals, for some core `Y`).

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

* `log` is the natural logarithm `Real.log`.
* The right-hand side is a real number and `W.card` is cast to `ℝ`.
* `k ≥ 2` is assumed: at `k = 1` we have `Real.log 1 = 0`, the right-hand side
  collapses to `0`, and the bound is false since `f (1, r) = r`. -/
theorem improved_sunflower_lemma {α : Type*} [DecidableEq α] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (W : Finset (Finset α)),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end Agent014
