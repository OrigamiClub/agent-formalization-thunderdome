import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

**Statement only.** Every theorem ends in `:= by sorry`; nothing is proved.
-/

namespace ImprovedSunflower

/-- A finite family `𝒮` of finite sets is a **sunflower with core `Y`** when any
two *distinct* members meet in exactly `Y`.

This is equivalent to the informal description: every element lying in at least
two members of `𝒮` lies in all of them, and the *petals* `S \ Y` for `S ∈ 𝒮`
are pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S₁ : Finset α⦄, S₁ ∈ 𝒮 → ∀ ⦃S₂ : Finset α⦄, S₂ ∈ 𝒮 → S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- `W` **contains a sunflower with `r` petals** when some subfamily `𝒮 ⊆ W`
having exactly `r` members (which are then automatically distinct, being elements
of a `Finset`) is a sunflower for some core `Y`. -/
def ContainsSunflower {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower 𝒮 Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang 2019; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C` such that for all integers `k ≥ 2` and `r ≥ 1`,
every finite family `W` of sets each of cardinality exactly `k` with
`(C * r * log k) ^ k < |W|` contains a sunflower with `r` petals.

Equivalently, the sunflower function `f` satisfies `f (k, r) ≤ (C * r * log k) ^ k`.

The constant `C` is quantified *before* the ambient type `α`, so it is genuinely
absolute: it does not depend on `α`, `k`, `r`, or `W`.

The hypothesis `2 ≤ k` sidesteps the degenerate case `k ≤ 1`, where `log k ≤ 0`
makes the right-hand side vanish or turn negative; for `k ≥ 2` we have
`Real.log k > 0` and the bound is a genuine positive threshold. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflower W r := by
  sorry

end ImprovedSunflower
