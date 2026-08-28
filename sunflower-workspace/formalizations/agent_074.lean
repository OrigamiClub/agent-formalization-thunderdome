import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

Statement only: the theorem is closed with `:= by sorry` and nothing is proved.
-/

/-- A `Finset` of sets `petals` forms a *sunflower with `r` petals and core `core`*
if it has exactly `r` (necessarily distinct, since it is a `Finset`) members, the
`core` is contained in every member, and any two distinct members intersect
exactly in `core`.

Consequences of this definition (for `r ≥ 2`): every element lying in at least two
members lies in all of them, and the petals `s \ core` for `s ∈ petals` are
pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (core : Finset α)
    (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
  (∀ ⦃s⦄, s ∈ petals → core ⊆ s) ∧
  (∀ ⦃s⦄, s ∈ petals → ∀ ⦃t⦄, t ∈ petals → s ≠ t → s ∩ t = core)

/-- **Improved sunflower lemma.**
There is an absolute constant `C` such that for every `k ≥ 2`, every `r ≥ 1`,
every ambient type `α`, and every finite family `W` of exactly-`k`-element subsets
of `α` whose size exceeds `(C · r · log k) ^ k`, the family `W` contains a
sunflower with `r` petals.

Equivalently, if `f(k, r)` denotes the least `N` such that any family of `N`
distinct `k`-sets contains an `r`-sunflower, then `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` for an arbitrary `α`; the family is `W : Finset (Finset α)`.
* `Real.log` is the natural logarithm; the base is irrelevant as it is absorbed
  into `C`.
* `C` is existentially quantified *outside* the quantifier over `α`, so it is
  genuinely absolute (independent of the ambient type).
* The hypothesis `2 ≤ k` avoids the degenerate case `k ≤ 1` where `Real.log k = 0`
  makes the right-hand side `0` and the statement false for `r ≥ 2`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * r * Real.log k) ^ k < (W.card : ℝ) →
          ∃ (P : Finset (Finset α)) (Y : Finset α), P ⊆ W ∧ IsSunflower r Y P := by
  sorry
