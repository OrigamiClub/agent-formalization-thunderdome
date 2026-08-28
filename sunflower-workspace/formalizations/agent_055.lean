import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the later refinements of Rao and of
Bell–Chueluecha–Warnke: writing `f(k, r)` for the sunflower function, one has
`f(k, r) ≤ (C · r · log k)^k` for an absolute constant `C`.

Equivalently: there is an absolute constant `C` such that for all positive integers
`k` and `r`, every finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C · r · log k)^k`, contains a sunflower with `r` petals.

This file gives the *statement* only; the proof is `sorry`.
-/

variable {α : Type*} [DecidableEq α]

/-- A finite family `𝒮` of finite sets is a **sunflower with core `Y`** when any two
distinct members of `𝒮` meet in exactly `Y`.

The "petals" are the differences `S \ Y` for `S ∈ 𝒮`.  This condition is equivalent
to saying that the petals are pairwise disjoint and that every point lying in two
members of the family already lies in `Y`, hence in every member. -/
def IsSunflower (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop :=
  ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y

/-- `𝒮` is a **sunflower with `r` petals**: it has exactly `r` members (automatically
pairwise distinct, since `𝒮 : Finset (Finset α)`) and it is a sunflower for some
core `Y`. -/
def IsSunflowerWithPetals (r : ℕ) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower Y 𝒮

/-- **Improved sunflower lemma (statement).**

There is an absolute constant `C > 0` such that for all positive integers `k` and
`r`, every finite family `W` of `k`-element sets with
`#W > (C · r · max 1 (Real.log k))^k` contains a sunflower with `r` petals.

Encoding decisions (see the accompanying `.md` note for rationale):

* Sets are `Finset α` over an ambient type with `DecidableEq`; the family `W` is a
  `Finset (Finset α)`, so distinctness of its members is automatic.
* `C` is bound existentially *inside* the theorem but *outside* the quantifier over
  the ambient type `α`, so it is genuinely an absolute constant.
* The logarithm is the natural logarithm `Real.log`.  To keep the bound
  non-degenerate at `k = 1` (where `Real.log 1 = 0`), the factor `log k` is taken
  as `max 1 (Real.log k)`; for `k ≥ 3` this equals `Real.log k`.
* The size comparison is performed in `ℝ`, coercing `W.card`.
* "Contains a sunflower with `r` petals" means: there is a subfamily `𝒮 ⊆ W` with
  `IsSunflowerWithPetals r 𝒮`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k < (W.card : ℝ) →
          ∃ 𝒮 ⊆ W, IsSunflowerWithPetals r 𝒮 := by
  sorry
