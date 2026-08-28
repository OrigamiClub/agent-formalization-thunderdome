import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the **statement only**; the proof is `sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `T` of finite sets is a **sunflower with `r` petals and core `Y`**
if it consists of exactly `r` sets (members of a `Finset` are automatically distinct),
any two distinct members of which intersect in exactly `Y`.

Consequences that are *not* part of the definition: every element lying in `≥ 2`
members lies in all of them, and the petals `s \ Y` for `s ∈ T` are pairwise
disjoint. When all members have a common finite cardinality and `r ≥ 2`, the core is
a proper subset of each member, so the petals are automatically nonempty. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop :=
  T.card = r ∧ ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang, refined by Rao and by
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all positive integers `k` and `r`,
every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` over an arbitrary ambient type `α`; the family `W` is a
  `Finset (Finset α)`, which supplies finiteness and distinctness of members.
* `C` is quantified outermost (before `α`), so it is genuinely absolute: one
  constant works for every ambient type and every `k, r`.
* `log` is the natural logarithm `Real.log`; the base is irrelevant since it only
  changes the absolute constant `C`.
* The cardinality comparison is done in `ℝ` after coercion. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        0 < k → 0 < r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ T ⊆ W, ∃ Y : Finset α, IsSunflower T r Y := by
  sorry

end ImprovedSunflower
