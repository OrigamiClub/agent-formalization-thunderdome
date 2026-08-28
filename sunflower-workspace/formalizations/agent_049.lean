import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the theorem ends in `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- A finite family `petals` of finite sets is a *sunflower* (a.k.a. Δ-system)
with core `core` when any two distinct members meet in exactly `core`.

Consequences of this definition (not needed for the statement): as soon as the
family has at least two members, `core ⊆ S` for every `S ∈ petals`, every element
lying in `≥ 2` members lies in all of them, and the petals `S \ core`
(`S ∈ petals`) are pairwise disjoint. -/
def IsSunflower (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  (petals : Set (Finset α)).Pairwise fun S T => S ∩ T = core

/-- `W` *contains a sunflower with `r` petals* when some `r`-element subfamily of
`W` is a sunflower with some core.

Distinctness of the `r` petals is automatic: the elements of a
`Finset (Finset α)` are pairwise distinct, so `𝒮.card = r` genuinely gives `r`
distinct sets. -/
def ContainsSunflower (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α),
    𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ core : Finset α, IsSunflower 𝒮 core

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C · r · log k) ^ k`, contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* `C` is existentially quantified *outside* the type family `α`, so it is a
  genuine absolute constant.
* `log` is the natural logarithm `Real.log`; the base is immaterial since it is
  absorbed into `C`.
* The hypothesis `2 ≤ k` avoids the degenerate case `k = 1` (where
  `Real.log 1 = 0` makes the right-hand side `0`) and `k = 0`.
* The cardinality comparison is stated in `ℝ` after coercing `W.card`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ContainsSunflower W r := by
  sorry

end ImprovedSunflower
