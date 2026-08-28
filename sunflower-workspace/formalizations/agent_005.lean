import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the quantitative refinements of Rao and of
Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The theorem is closed with `sorry`; nothing is
proved.
-/

/-- A subfamily `S` of finite sets is a *sunflower with `r` petals* when it consists of
exactly `r` sets (the `Finset (Finset α)` structure makes them automatically distinct, and
`S.card = r` pins the count) whose pairwise intersections all coincide with a single *core*
`Y`.

Equivalently, the *petals* `A \ Y` for `A ∈ S` are pairwise disjoint, and every element
that lies in two members of `S` lies in every member of `S`.  Those equivalent phrasings are
consequences of the definition below and are not stated separately.

For `r ≤ 1` the `∃ Y` clause is vacuous (there are no two distinct members), so every family
of at most one set is trivially a sunflower; for `r ≥ 2` the core `Y` is forced to be the
common intersection `⋂ S`. -/
def IsSunflowerWithPetals {α : Type*} [DecidableEq α]
    (r : ℕ) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ ∃ Y : Finset α, ∀ ⦃A⦄, A ∈ S → ∀ ⦃B⦄, B ∈ S → A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that, for all positive integers `k` and `r`, every
finite family `W` of sets each of cardinality exactly `k` with
`#W > (C · r · log k)^k` contains a sunflower with `r` petals.

Encoding notes:
* The ambient type `α` is arbitrary; members of `W` are `Finset α`, hence finite sets, and
  `W : Finset (Finset α)` is a finite family whose members are automatically distinct.
* `Real.log` is the natural logarithm.  The base is immaterial: changing it rescales the
  `log` factor by a constant, which the existentially quantified `C` absorbs.
* The factor is `Real.log k + 1` rather than bare `Real.log k`.  This guards the degenerate
  values: at `k = 1` we have `Real.log 1 = 0`, and the true sunflower function satisfies
  `f(1, r) = r`, so the bound must stay `≥ r`; the `+ 1` delivers exactly `C · r` there.
  For `k ≥ 2` one has `Real.log k + 1 ≤ (1 + (Real.log 2)⁻¹) · Real.log k`, so the bound
  changes only by a factor bounded independently of `k`, again absorbed into `C`.
* `C` is existentially quantified inside the statement, together with its positivity. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ A ∈ W, A.card = k) →
          (W.card : ℝ) > (C * (r : ℝ) * (Real.log (k : ℝ) + 1)) ^ k →
          ∃ S ⊆ W, IsSunflowerWithPetals r S := by
  sorry
