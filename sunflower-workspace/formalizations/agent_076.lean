import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The theorem is closed with `sorry`.
-/

open scoped Classical

/-- A finite family `𝒮` of sets is a *sunflower* (also called a Δ-system) with
*core* `Y` when every two distinct members of `𝒮` intersect exactly in `Y`.

Facts that follow from this definition (and are therefore not part of it):
every element that lies in at least two members of `𝒮` lies in all of them, and
the *petals* `A \ Y` for `A ∈ 𝒮` are pairwise disjoint.

The number of petals is the number of members of `𝒮`, i.e. `𝒮.card`; the members
of a `Finset` are automatically pairwise distinct, so no separate distinctness
hypothesis is needed. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒮 → ∀ ⦃B⦄, B ∈ 𝒮 → A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of sets each of cardinality exactly `k`, with
`|W| > (C · r · log k) ^ k`, contains a *sunflower with `r` petals*: an
`r`-element subfamily `𝒮 ⊆ W` for which there is a core `Y` with
`A ∩ B = Y` for all distinct `A, B ∈ 𝒮`.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family is `Finset (Finset α)`.
  `α` (and its `DecidableEq`) is quantified *inside* the statement so that the
  single constant `C` is genuinely absolute (independent of `α`).
* `log` is `Real.log`, the natural logarithm.  Only the constant `C` changes if a
  different base is used, so the choice of base is immaterial to the statement.
* The right-hand side is compared with `W.card` coerced to `ℝ`.
* `k = 0` and `k = 1` are excluded by `2 ≤ k`.  For those `k` the bound
  `(C · r · log k) ^ k` degenerates to `0`, and the sunflower function does not
  have this shape there (for `k = 1` it is exactly `r`).
* Petals are not required to be nonempty; since the `r` members are distinct and
  all have the same cardinality `k`, at most one of them can equal the core, so
  at least `r - 1` petals are automatically nonempty.

Equivalently: the sunflower function `f` satisfies `f (k, r) ≤ (C · r · log k) ^ k`
for `k ≥ 2`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ A ∈ W, A.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ 𝒮 : Finset (Finset α),
            𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower 𝒮 Y := by
  sorry
