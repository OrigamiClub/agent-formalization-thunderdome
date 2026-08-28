import Mathlib

/-!
# Improved sunflower lemma — statement only

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

Everything is placed in the `Agent044` namespace so that the auxiliary
definitions cannot clash with anything Mathlib may already provide
(`Finset.IsSunflower` / `Finset.IsSunflowerWith` / `Finset.exists_sunflower`).
-/

namespace Agent044

variable {α : Type*}

/-- `IsSunflowerWith P r Y` states that the finite family of finsets `P` forms a
*sunflower with `r` petals* and *core* `Y`:

* `P` has exactly `r` members, its petals (they are automatically distinct,
  being elements of a `Finset`);
* every petal contains the core `Y`;
* any two distinct petals meet exactly in `Y`.

The last condition is equivalent to: the sets `S \ Y` for `S ∈ P` are pairwise
disjoint, and every point lying in at least two petals lies in all of them.
Empty petals are permitted (by distinctness at most one petal can be empty). -/
structure IsSunflowerWith [DecidableEq α]
    (P : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop where
  /-- the family has exactly `r` petals -/
  card_petals : P.card = r
  /-- every petal contains the core -/
  core_subset : ∀ ⦃S : Finset α⦄, S ∈ P → Y ⊆ S
  /-- distinct petals intersect exactly in the core -/
  pairwise_inter : ∀ ⦃S : Finset α⦄, S ∈ P → ∀ ⦃T : Finset α⦄, T ∈ P → S ≠ T →
    S ∩ T = Y

/-- `W` *contains a sunflower with `r` petals* if some subfamily of `W` is a
sunflower with `r` petals (for some core `Y`). -/
def ContainsSunflowerWith [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ P ⊆ W, ∃ Y : Finset α, IsSunflowerWith P r Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang 2019; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every type `α` with
decidable equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family
`W` of finsets of `α` each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then `W` contains a sunflower with `r` petals.

* `log` is the natural logarithm `Real.log`.
* The hypothesis `2 ≤ k` sidesteps the degenerate case `log 1 = 0`.
* The comparison is stated over `ℝ` after coercing `r`, `k` and `W.card`.

Equivalently: the sunflower function `f` satisfies `f (k, r) ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] {k r : ℕ}, 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflowerWith W r := by
  sorry

end Agent044
