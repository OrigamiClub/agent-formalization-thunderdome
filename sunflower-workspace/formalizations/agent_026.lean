import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

universe u

namespace ImprovedSunflower

/-- A **sunflower with `r` petals and core `Y`** inside an ambient type `α`.

`𝒮` is a family of exactly `r` sets (they are automatically pairwise distinct,
since `𝒮 : Finset (Finset α)` and `𝒮.card = r`), each of which contains the core
`Y`, and such that any two distinct members of the family meet in exactly `Y`.

The *petals* are the sets `S \ Y` for `S ∈ 𝒮`. The stated conditions force the
petals to be pairwise disjoint, and any element lying in two members of `𝒮` in
fact lies in `Y`, hence in every member. Petals are allowed to be empty. -/
def IsSunflower {α : Type u} [DecidableEq α]
    (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧
  (∀ S ∈ 𝒮, Y ⊆ S) ∧
  (∀ S₁ ∈ 𝒮, ∀ S₂ ∈ 𝒮, S₁ ≠ S₂ → S₁ ∩ S₂ = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for every integer `k ≥ 2`, every
integer `r ≥ 1`, and every finite family `W` of sets each of cardinality exactly
`k`, if
`|W| > (C · r · log k) ^ k`
then some subfamily `𝒮 ⊆ W` is a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family is `W : Finset (Finset α)`.
* `log` is the natural logarithm `Real.log`; the choice of base only changes `C`.
* The constant `C` is existentially quantified *outside* the quantifier over `α`,
  `k`, `r`, `W`, so it is genuinely absolute.
* `k ≥ 2` avoids the degenerate cases `k = 0` (`log 0`) and `k = 1` (`log 1 = 0`),
  where the right-hand side collapses. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type u} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (𝒮 : Finset (Finset α)),
          𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry

end ImprovedSunflower
