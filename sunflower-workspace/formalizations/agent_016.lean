import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains the *statement* only. The theorem ends with `:= by sorry`.
-/

open scoped BigOperators

/-- A family `S` of finite sets is a **sunflower with core `Y`** if every two
distinct members meet exactly in `Y`. Equivalently, the "petals" `s \ Y` for
`s ∈ S` are pairwise disjoint, and every element lying in two members lies in
all of them.

When `S.card = r` (and `r ≥ 2`) this is a "sunflower with `r` petals";
for `r ≥ 2` the core satisfies `Y ⊆ s` for every `s ∈ S`. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁ ∩ s₂ = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals: a subfamily
`S ⊆ W` with `|S| = r` and a common core `Y` with `s₁ ∩ s₂ = Y` for all
distinct `s₁, s₂ ∈ S`.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family is `W : Finset (Finset α)`.
* `log` is the natural logarithm `Real.log`; the cardinality bound is stated
  over `ℝ` with the obvious `ℕ → ℝ` casts.
* `C` is existentially quantified (an absolute constant), together with `0 < C`.
* The regime `k ≥ 2` is imposed so that `Real.log k > 0`; the excluded case
  `k = 1` (where `log k = 0`) is elementary and handled separately in the
  literature.
* Distinctness of the `r` members of the sunflower is automatic from
  `S : Finset _` together with `S.card = r`. Petals are not required to be
  nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ S ⊆ W, S.card = r ∧ ∃ Y : Finset α, IsSunflower S Y := by
  sorry
