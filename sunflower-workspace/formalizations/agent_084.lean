/-
Improved sunflower lemma — statement only.

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao ("Coding for sunflowers")
and by Bell–Chueluecha–Warnke.

This file states the theorem and ends with `:= by sorry`.  Nothing is proved.

As of this Mathlib, there is no `Sunflower` file in `Mathlib/Combinatorics/`
(`grep -ri sunflower` over the source tree returns nothing), so the sunflower
predicate is defined here from scratch.
-/
import Mathlib

namespace ImprovedSunflower

variable {α : Type*}

/-- `IsSunflower 𝒮 Y` : the finite family of finsets `𝒮` is a **sunflower with
core `Y`**, i.e. any two distinct members of `𝒮` meet exactly in `Y`.

Consequences of this condition (for `𝒮` with at least two members, hence not
separately assumed here):

* every element lying in `≥ 2` members lies in all of them;
* `Y ⊆ S` for every `S ∈ 𝒮`;
* the *petals* `S \ Y`, for `S ∈ 𝒮`, are pairwise disjoint. -/
def IsSunflower [DecidableEq α] (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y

/-- `IsSunflowerWith 𝒮 r` : `𝒮` is a **sunflower with `r` petals** — it has
exactly `r` (necessarily distinct, as members of a `Finset`) sets and admits some
core `Y`. -/
def IsSunflowerWith [DecidableEq α] (𝒮 : Finset (Finset α)) (r : ℕ) : Prop :=
  𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower 𝒮 Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every ambient type `α`, every
`r ≥ 1` and every `k ≥ 2`, every finite family `W` of `k`-element finsets of `α`
with
`(C * r * Real.log k) ^ k < |W|`
contains a subfamily `𝒮 ⊆ W` that is a sunflower with `r` petals.

Equivalently: the sunflower function obeys `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` for an arbitrary `α : Type`; the family `W` is a
  `Finset (Finset α)`, so its members are automatically distinct and `W.card`
  is `|W|`.
* `C` is existentially quantified *outside* the quantifier over `α`, so it is a
  genuine absolute constant (independent of the ambient type).
* The logarithm is `Real.log` (natural log); the size bound is compared in `ℝ`
  via the cast `(W.card : ℝ)`.
* The hypothesis `2 ≤ k` is imposed because at `k = 1` one has `Real.log 1 = 0`
  while `f (1, r) = r`, so the `(C r log k) ^ k` form is only correct for
  `k ≥ 2` (this matches the statements in the literature).  `k = 0` is excluded
  a fortiori. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type) [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ IsSunflowerWith 𝒮 r := by
  sorry

end ImprovedSunflower
