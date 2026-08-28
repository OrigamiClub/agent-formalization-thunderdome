/-
Improved sunflower lemma -- STATEMENT ONLY.

Alweiss-Lovett-Wu-Zhang (2019), with the bound refined by Rao and by
Bell-Chueluecha-Warnke.

This file contains only the statement, terminated by `:= by sorry`.
Nothing is proved.
-/
import Mathlib

namespace ImprovedSunflowerLemma

/-- A *sunflower with `r` petals and core `Y`* is a finite family `P` of finite
sets such that

* `P` has exactly `r` members -- they are automatically distinct, being
  elements of a `Finset`;
* any two distinct members of `P` meet in exactly the core `Y`.

For `r ≥ 2` this already forces `Y ⊆ S` for every `S ∈ P` (since
`Y = S₁ ∩ S₂ ⊆ S₁`) and makes the petals `S \ Y` (`S ∈ P`) pairwise disjoint,
which is the usual informal description: every element lying in at least two
members of the family lies in the core, hence in all of them. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃S₁ : Finset α⦄, S₁ ∈ P → ∀ ⦃S₂ : Finset α⦄, S₂ ∈ P → S₁ ≠ S₂ →
      S₁ ∩ S₂ = Y

/-- **Improved sunflower lemma** (Alweiss-Lovett-Wu-Zhang 2019; bound refined by
Rao and by Bell-Chueluecha-Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, and every finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C * r * log k) ^ k` then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C * r * log k) ^ k`.

Encoding decisions:

* `C` is existentially quantified *before* the quantifier over the ambient type
  `α`, so it is genuinely an absolute constant (independent of `α`, `k`, `r`,
  `W`).
* Sets are `Finset α` for an arbitrary ambient type `α` with decidable
  equality; the family `W` is a `Finset (Finset α)`.
* `log` is the natural logarithm `Real.log`; the size comparison is carried out
  in `ℝ` after casting `W.card` and `k`.
* The hypothesis `2 ≤ k` is imposed because `Real.log 1 = 0` makes the bound
  degenerate (and false) at `k = 1`; the statement in the literature is
  likewise understood for `k ≥ 2`.
* The returned sunflower `P` is a sub-family of `W` (`P ⊆ W`); its members
  therefore automatically have cardinality `k`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)),
            P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end ImprovedSunflowerLemma
