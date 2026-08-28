import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), later refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the **statement only**; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A family `𝒮` of finsets is a **sunflower with `r` petals** with **core `Y`** when

* it consists of exactly `r` distinct sets (`card_petals : 𝒮.card = r`);
* `Y` is contained in every member (`core_subset`);
* any two distinct members meet in exactly `Y` (`pairwise_inter`).

The petals `S \ Y` for `S ∈ 𝒮` are then automatically pairwise disjoint
(`(S \ Y) ∩ (T \ Y) = (S ∩ T) \ Y = Y \ Y = ∅` for `S ≠ T`), and every element lying
in two members lies in all of them. -/
structure IsSunflower (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop where
  /-- The sunflower has exactly `r` (distinct) petals. -/
  card_petals : 𝒮.card = r
  /-- The core is contained in every petal. -/
  core_subset : ∀ S ∈ 𝒮, Y ⊆ S
  /-- Any two distinct petals intersect in exactly the core. -/
  pairwise_inter : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every type `α` with decidable
equality, all positive integers `k` and `r`, and every finite family `W` of
`k`-element finsets of `α` with `|W| > (C · r · log (k + 1)) ^ k`, the family `W`
contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C · r · log (k + 1)) ^ k`.

Encoding notes:

* `Real.log (k + 1)` is used rather than `Real.log k`, so that the bound is still
  meaningful at `k = 1` (where `Real.log 1 = 0`). For `k ≥ 2` this weakens the bound
  only by a bounded factor, which the existential constant `C` absorbs; hence this is
  equivalent to the usual `(C · r · log k) ^ k` formulation.
* `C` is existentially quantified at the very front, so it depends on nothing
  (in particular not on `α`, `k`, `r`, or `W`).
* Distinctness of the members of `W`, and of the `r` petals, is automatic from the
  use of `Finset (Finset α)`.
* Petals are not required to be nonempty (i.e. `Y` may equal some member); this is
  irrelevant once `r ≥ 2` and `k ≥ 1`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
            ∃ (Y : Finset α) (𝒮 : Finset (Finset α)), 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry

end ImprovedSunflower
