import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao ("Coding for Sunflowers")
and by Bell–Chueluecha–Warnke.

This file contains the *statement only*. Nothing is proved.
-/

/-- A finite family `P` of finite sets is a **sunflower** (Δ-system) with **core**
`Y` when any two distinct members of `P` intersect exactly in `Y`.

This is equivalent to the usual formulation: the **petals** `S \ Y`, for `S ∈ P`,
are pairwise disjoint, and every element that lies in at least two members of `P`
lies in all of them.  When `2 ≤ P.card` the core `Y` is uniquely determined and
`Y ⊆ S` for every `S ∈ P`; distinct members then force every petal to be
nonempty.

The **number of petals** of the sunflower is `P.card`. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ P → ∀ ⦃T⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for all positive integers `k` and `r`,
every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals — i.e. a
subfamily `P ⊆ W` consisting of exactly `r` (necessarily distinct, since `P` is a
`Finset`) sets that share a common core `Y`.

Encoding choices:
* Sets are `Finset`s over an ambient type `α` with decidable equality; the family
  `W` is a `Finset (Finset α)`.
* Cardinalities are `Finset.card`; the final size comparison is cast into `ℝ`.
* `log` is the natural logarithm `Real.log`.
* `C` is existentially quantified together with its positivity.
* `k, r` are only assumed positive (`0 < k`, `0 < r`), matching "positive
  integers" literally.  (For `k = 1` one has `Real.log 1 = 0`, so the hypothesis
  becomes `0 < |W|`; the statement is genuine content only for `k ≥ 2`, where
  `log k > 0`.)

Equivalently: the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧
              ∃ Y : Finset α, IsSunflower P Y := by
  sorry
