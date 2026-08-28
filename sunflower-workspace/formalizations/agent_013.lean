import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke: there is an absolute constant `C` such that the
sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Equivalently: every finite family of `k`-element sets of size exceeding
`(C · r · log k) ^ k` contains a sunflower with `r` petals.

This file gives the **statement only**; every theorem ends in `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `𝓢` of finsets is a **sunflower with core `Y`** when any two
*distinct* members meet exactly in `Y`.  Consequently the petals `A \ Y`
(`A ∈ 𝓢`) are pairwise disjoint, and any element lying in two members lies in
every member.  Encoding the family as a `Finset (Finset α)` builds in the
distinctness of its members. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (𝓢 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝓢 → ∀ ⦃B⦄, B ∈ 𝓢 → A ≠ B → A ∩ B = Y

/-- `W` **contains a sunflower with `r` petals** if some subfamily consisting of
exactly `r` (hence distinct) members of `W` is a sunflower for some core `Y`. -/
def ContainsSunflower {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ (𝓢 : Finset (Finset α)) (Y : Finset α),
    𝓢 ⊆ W ∧ 𝓢.card = r ∧ IsSunflower 𝓢 Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao;
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every type `α`, all positive
integers `k` and `r`, and every finite family `W` of subsets of `α` each of
cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k`
then `W` contains a sunflower with `r` petals.

Notes on the encoding:
* `C` is existentially quantified *outside* the quantifier over `α, k, r, W`, so
  it is genuinely absolute.
* The logarithm is the natural logarithm `Real.log`.  The factor `log k` is read
  as `max 1 (Real.log k)`; this keeps the bound meaningful (and the statement
  true) at `k = 1`, where `Real.log 1 = 0`, and agrees with `Real.log k` for all
  `k ≥ 3`.  Absorbing this into the absolute constant is standard.
* Cardinalities use `Finset.card`, cast to `ℝ` to compare with the real-valued
  bound. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ A ∈ W, A.card = k) →
          ((C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k : ℝ) < (W.card : ℝ) →
          ContainsSunflower W r := by
  sorry

/-- Restatement in terms of an explicit sunflower function `f`, i.e. the least
size forcing a sunflower with `r` petals among `k`-sets.  With `f` supplied as a
hypothesis characterising that threshold, the improved bound reads
`f k r ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
      ∀ W : Finset (Finset α), (∀ A ∈ W, A.card = k) → f k r ≤ W.card →
        ContainsSunflower W r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k r : ℕ, 0 < k → 0 < r →
        (f k r : ℝ) ≤ (C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k := by
  sorry

end ImprovedSunflower
