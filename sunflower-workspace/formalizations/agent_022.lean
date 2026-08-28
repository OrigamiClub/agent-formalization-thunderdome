import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains **only the statement**; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `𝒮` of finite sets is a **sunflower with core `Y`** if any
two *distinct* members of `𝒮` meet exactly in `Y`.

Equivalently: every element lying in at least two members of `𝒮` lies in all of
them, and the *petals* `S \ Y` (`S ∈ 𝒮`) are pairwise disjoint.  As soon as
`𝒮` has two distinct members this pins down `Y` as their common intersection and
forces `Y ⊆ S` for every `S ∈ 𝒮`, so no separate `Y ⊆ S` clause is needed. -/
def IsSunflower [DecidableEq α] (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y

/-- `W` **contains a sunflower with `r` petals** if some subfamily `𝒮 ⊆ W` of
cardinality exactly `r` is a sunflower for some core `Y`.

The `r` sets of the sunflower are automatically pairwise distinct because
`𝒮 : Finset (Finset α)` and `𝒮.card = r`. -/
def HasSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ ∃ Y : Finset α, 𝒮.card = r ∧ IsSunflower 𝒮 Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every `k ≥ 2`, every
`r ≥ 1`, every type `α` with decidable equality, and every finite family `W` of
subsets of `α` each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then `W` contains a sunflower with `r` petals.

Encoding notes:
* `log` is the natural logarithm `Real.log`; the choice of base is immaterial
  since a base change only rescales `C`.
* `C` is existentially quantified *outside* the quantifier over `α`, so it is a
  genuine absolute constant, independent of the ambient type.
* The hypothesis `2 ≤ k` sidesteps the degenerate case `k = 1`, where
  `Real.log k = 0` makes the right-hand side `0`; for `k = 1` the statement is
  anyway trivial, since any `r` distinct singletons form a sunflower with empty
  core.
* `|W|`, `k` and `r` are `ℕ`; the inequality is stated in `ℝ` with the obvious
  coercions.  `x ^ k` is the monoid power (natural exponent).
* Reformulated with the sunflower function `f`, this says
  `f (k, r) ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

end ImprovedSunflower
