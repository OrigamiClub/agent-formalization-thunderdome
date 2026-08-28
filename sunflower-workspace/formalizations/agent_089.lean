import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The single theorem is closed with `sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `petals` of finite subsets of `α` is a **sunflower with core `core`**
when any two distinct members of the family meet in exactly `core`.

This is the definition from the problem statement: there is a core set `Y` with
`Sᵢ ∩ Sⱼ = Y` for every `i ≠ j`.  Its stated consequences follow:
every element contained in at least two members is contained in all of them, and the
petals `A \ core` (`A ∈ petals`) are pairwise disjoint.

Distinctness of the members and the fact that they all have the same cardinality are not
part of this predicate; in the theorem below they are supplied by `petals ⊆ W`,
`petals.card = r` (a `Finset` has no repeats) and the uniformity hypothesis on `W`. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ petals → ∀ ⦃B⦄, B ∈ petals → A ≠ B → A ∩ B = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k` and `r`,
every finite family `W` of sets each of cardinality exactly `k`, with

`|W| > (C · r · log (k + 1)) ^ k`,

contains a sunflower with `r` petals: an `r`-element subfamily `P ⊆ W` and a core `Y`
such that any two distinct members of `P` intersect in exactly `Y`.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log (k + 1)) ^ k`.

Encoding notes.
* Sets are `Finset α` over an arbitrary ambient type `α` with decidable equality; the
  family `W` is a `Finset (Finset α)`, so its members are automatically distinct.
* `Real.log` is used for the logarithm; its base is irrelevant here, being absorbed
  into `C`.
* `Real.log ((k : ℝ) + 1)` is used rather than `Real.log k` so that the statement is
  also true (not vacuously false) at `k = 1`, where `Real.log 1 = 0`.  The `+ 1` is
  absorbed into `C` and does not change the asymptotics.
* `C` is existentially quantified inside the theorem, capturing "there is an absolute
  constant". -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 1 ≤ k → 1 ≤ r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ A ∈ W, A.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ (P : Finset (Finset α)) (Y : Finset α),
            P ⊆ W ∧ P.card = r ∧ IsSunflower P Y := by
  sorry

end ImprovedSunflower
