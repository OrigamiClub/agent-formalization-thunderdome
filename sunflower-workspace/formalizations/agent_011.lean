import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao ("Coding for Sunflowers") and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*.  Every theorem ends in `:= by sorry`; nothing is proved.
-/

namespace ImprovedSunflower

/-- `IsSunflower 𝒮 r` states that the finite family `𝒮` of finite sets is a
*sunflower with `r` petals*:

* `𝒮` consists of exactly `r` sets (as a `Finset`, its members are automatically distinct), and
* there is a common **core** `Y` such that any two *distinct* members of `𝒮` meet exactly in `Y`.

The **petals** are the sets `A \ Y` for `A ∈ 𝒮`.  From the condition, every element lying in `≥ 2`
members lies in `Y` (hence, for `r ≥ 2`, in all members), and the petals are pairwise disjoint.
Petals are here allowed to be empty (for `r ≥ 2` at most one petal can be empty). -/
def IsSunflower {α : Type*} [DecidableEq α] (𝒮 : Finset (Finset α)) (r : ℕ) : Prop :=
  𝒮.card = r ∧ ∃ Y : Finset α, ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`, every finite
family `W` of sets each of cardinality exactly `k` with

  `(C * r * Real.log k) ^ k  <  |W|`

contains a sunflower with `r` petals (a subfamily `𝒮 ⊆ W` with `IsSunflower 𝒮 r`).

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * log k) ^ k`.

Encoding notes:
* Sets are `Finset α` for an ambient type `α`; the family `W` is a `Finset (Finset α)`, so its
  members are automatically distinct and `|W| = W.card`.
* The constant `C` is existentially quantified inside the statement ("there is an absolute
  constant").
* `Real.log` is used; the base is irrelevant since it is absorbed into `C`.
* `k ≥ 2` is assumed so that `Real.log k > 0` (avoiding the degenerate `Real.log 1 = 0`, for
  which the displayed bound is false). `r ≥ 1` makes `r`-petal sunflowers meaningful. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ A ∈ W, A.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ 𝒮 ⊆ W, IsSunflower 𝒮 r := by
  sorry

end ImprovedSunflower
