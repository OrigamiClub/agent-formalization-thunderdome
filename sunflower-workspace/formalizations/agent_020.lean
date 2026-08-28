import Mathlib

/-!
# Improved sunflower lemma — statement only

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.
-/

/-- A **sunflower with `r` petals** and core `core`: a finite family `petals` of exactly `r`
distinct sets whose pairwise intersections all equal `core`.

Automatic consequences (deliberately *not* baked into the definition):
* if `2 ≤ r`, then `core ⊆ S` for every `S ∈ petals` (take another petal `T ≠ S`, then
  `core = S ∩ T ⊆ S`);
* the sets `S \ core` for `S ∈ petals` are pairwise disjoint (if `x` lies in two of them,
  then `x ∈ S ∩ T = core`, contradiction). -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (core : Finset α)
    (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
    ∀ ⦃S⦄, S ∈ petals → ∀ ⦃T⦄, T ∈ petals → S ≠ T → S ∩ T = core

/-- **Improved sunflower lemma.**
There is an absolute constant `C` such that for all integers `k ≥ 2` and `r ≥ 1`, every finite
family `W` of sets each of cardinality exactly `k` with `|W| > (C · r · log k)^k` contains a
sunflower with `r` petals (i.e. some subfamily `P ⊆ W` with a core `core` such that `P` is a
sunflower with `r` petals).

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`.

Encoding notes:
* `log` is the natural logarithm `Real.log`; the base is irrelevant since it is absorbed into `C`.
* The hypothesis `2 ≤ k` avoids the degenerate case `k = 1`, where `Real.log k = 0` makes the
  bound `0` and the statement is false for `r ≥ 2` (a family of `> 0` singletons need not contain
  two distinct sets).
* Sets are `Finset α` over an arbitrary ambient type; the family is `W : Finset (Finset α)`.
* Distinctness of the `r` petals is encoded by `petals.card = r` in `IsSunflower`. -/
theorem improved_sunflower_lemma {α : Type*} [DecidableEq α] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (W : Finset (Finset α)), (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ (core : Finset α) (P : Finset (Finset α)),
              P ⊆ W ∧ IsSunflower r core P := by
  sorry
