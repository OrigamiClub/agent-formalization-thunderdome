import Mathlib

/-!
# Statement of the improved sunflower lemma

(Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by Bell–Chueluecha–Warnke.)

This file contains only the *statement*. The theorem ends with `:= by sorry`.

## Encoding

* Sets are `Finset α` over an ambient type `α` with `DecidableEq α` (so that `∩`
  and `\` on `Finset` are available). A family of sets is a `Finset (Finset α)`;
  membership of a `Finset` automatically makes the members distinct, so no
  separate distinctness hypothesis is needed.
* A *sunflower with core `Y`* is captured by `IsSunflower` below: every pairwise
  intersection of distinct members equals `Y` (and `Y` is contained in each
  member). "`r` petals" is encoded as `S.card = r`.
* The bound uses the natural logarithm `Real.log` applied to `(k : ℝ)`. To avoid
  the degenerate regime where `Real.log k ≤ 0` (namely `k ∈ {0, 1}`), the
  hypothesis `2 ≤ k` is assumed; `k = 1` is a triviality handled separately in
  the informal statement.
* The absolute constant `C` is existentially quantified at the front
  ("there is an absolute constant `C`").
-/

open scoped BigOperators

/-- `S` is a *sunflower with core `Y`*: the core is contained in every member of
`S`, and every intersection of two distinct members of `S` is exactly `Y`.
Consequently the petals `A \ Y` for `A ∈ S` are pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ A ∈ S, Y ⊆ A) ∧ (∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y)

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for all positive integers `k`
(here `k ≥ 2`) and `r`, every finite family `W` of sets each of cardinality
exactly `k` with `|W| > (C · r · log k) ^ k` contains a sunflower with `r`
petals: a subfamily `S ⊆ W` with `|S| = r` and a core `Y` such that all pairwise
intersections of members of `S` equal `Y`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        1 ≤ r → 2 ≤ k →
        (∀ A ∈ W, A.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ S : Finset (Finset α), S ⊆ W ∧ S.card = r ∧ ∃ Y : Finset α, IsSunflower S Y := by
  sorry
