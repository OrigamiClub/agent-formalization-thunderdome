import Mathlib

namespace Agent018

/-- A finite family `𝒜` of finsets forms a **sunflower with core `Y`** when
`Y` is contained in every member and every two *distinct* members meet exactly
in `Y`.  The *petals* are the sets `S \ Y` for `S ∈ 𝒜`; the condition
`S ∩ T = Y` for `S ≠ T` forces the petals to be pairwise disjoint, and every
element lying in two members lies in `Y`, hence in all of them.  The number of
petals is `𝒜.card` (members of a `Finset` are automatically distinct).

The `core_subset` field is redundant as soon as `2 ≤ 𝒜.card` (then
`Y = S ∩ T ⊆ S` for each member `S`), but it pins the core down in the
degenerate cases `𝒜.card ≤ 1`. -/
structure IsSunflower {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (Y : Finset α) : Prop where
  core_subset : ∀ ⦃S⦄, S ∈ 𝒜 → Y ⊆ S
  pairwise_inter : ∀ ⦃S⦄, S ∈ 𝒜 → ∀ ⦃T⦄, T ∈ 𝒜 → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all positive integers `k`
and `r`, every finite family `W` of sets each of cardinality exactly `k`
with `|W| > (C · r · log (k + 1))^k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log (k+1))^k`.

Encoding choices (see the accompanying `.md` note):
* Sets are `Finset`s over an arbitrary ambient type `α`; the family `W` is a
  `Finset (Finset α)`.  Distinctness of members and "exactly `r` petals" are
  captured by `𝒜.card = r` together with `𝒜 ⊆ W`.
* `Real.log` is the natural logarithm; the choice of base only rescales `C`.
* The logarithm is taken at `k + 1`, not `k`, so that the statement is true
  for every positive `k`: at `k = 1` one would otherwise have
  `(C · r · log 1)^1 = 0 < |W|` for any nonempty `W`, which is false.
  For large `k` replacing `log k` by `log (k+1)` only changes the constant.
* `C` is existentially quantified inside the theorem, so the statement is a
  closed proposition with no free parameters.
* Petals are automatically nonempty when `2 ≤ r`: a member equal to the core
  would, by uniform cardinality `k`, coincide with every other member. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ 𝒜 ⊆ W, ∃ Y : Finset α, 𝒜.card = r ∧ IsSunflower 𝒜 Y := by
  sorry

end Agent018
