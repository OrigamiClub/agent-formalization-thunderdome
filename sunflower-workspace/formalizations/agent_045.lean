import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke: there is an absolute constant `C` such that any family of
`> (C · r · log k)^k` many `k`-element sets contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/

open scoped BigOperators

/-- A subfamily `𝒮` of finite sets is a **sunflower with `r` petals** if it has
exactly `r` members and there is a common *core* `Y` such that any two distinct
members meet in exactly `Y`.

Consequences (not part of the definition, but equivalent to it for `r ≥ 2`):
every element lying in two members lies in `Y`, so `Y ⊆ S` for every `S ∈ 𝒮`, and
the petals `S \ Y` are pairwise disjoint.  Distinctness of the members is
automatic because `𝒮 : Finset (Finset α)`.  Petals are allowed to be empty. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧
    ∃ Y : Finset α, ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**  There is an absolute constant `C > 0` such that
for all integers `k ≥ 2` and `r ≥ 1`, every finite family `W` of sets of size
exactly `k` with more than `(C · r · log k)^k` members contains a sunflower with
`r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient `DecidableEq` type; the family is
  `W : Finset (Finset α)`.  `α` is quantified *inside* the existential for `C`,
  so `C` is genuinely absolute (independent of the ground type).
* `log` is the natural logarithm `Real.log`; any other base only rescales `C`.
* The regime `k ≤ 1` (where `Real.log k ≤ 0` makes the bound degenerate) is
  excluded by `2 ≤ k`.
* "Contains a sunflower with `r` petals" is `∃ 𝒮 ⊆ W, IsSunflower r 𝒮`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ 𝒮 ⊆ W, IsSunflower r 𝒮 := by
  sorry

/-- Restatement in terms of the sunflower function `f k r`, defined as the least
`N` such that every family of more than `N` sets of size `k` has a sunflower with
`r` petals: `f k r ≤ (C · r · log k)^k`.  Here it is phrased as a bound on any
`f` satisfying the defining property, to avoid committing to a definition of `f`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      (∀ S ∈ W, S.card = k) → f k r < W.card → ∃ 𝒮 ⊆ W, IsSunflower r 𝒮) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 2 ≤ k → 1 ≤ r →
      (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry
