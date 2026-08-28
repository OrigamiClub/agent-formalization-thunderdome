/-
Agent 093 — Formalization of the *statement* of the improved sunflower lemma.

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke:

  There is an absolute constant `C` such that for all `k ≥ 2` and `r ≥ 1`,
  every finite family `W` of sets, each of size exactly `k`, with
  `|W| > (C · r · log k) ^ k`, contains a sunflower with `r` petals.

Statement only: the theorem ends in `:= by sorry`.
-/
import Mathlib

namespace Agent093

/-- A finite subfamily `S` of sets is a **sunflower with `r` petals** when it has
exactly `r` (necessarily distinct) members and there is a common *core* `Y` such
that every two distinct members meet exactly in `Y`.

Consequences of this condition (so they need not be stated separately):
* every element lying in two members lies in `Y`, hence in every member;
* the *petals* `A \ Y` for `A ∈ S` are pairwise disjoint.

Petals are allowed to be empty (at most one member can equal the core). -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ ∃ Y : Finset α, ∀ ⦃A⦄, A ∈ S → ∀ ⦃B⦄, B ∈ S → A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and
by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that: for every type `α` with
decidable equality, every `k ≥ 2`, every `r ≥ 1`, and every finite family
`W : Finset (Finset α)` all of whose members have exactly `k` elements, if

  `(C * r * Real.log k) ^ k < W.card`

then `W` contains a subfamily `S ⊆ W` that is a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient `α`; the family is `W : Finset (Finset α)`,
  so no separate finiteness or distinctness hypotheses are needed.
* `C` is existentially quantified *outside* the quantifier over `α`, `k`, `r`,
  `W`, expressing that it is a single absolute constant.
* `Real.log` is the natural logarithm; the base is irrelevant since it can be
  absorbed into `C`.
* `k ≥ 2` sidesteps the degenerate case `k = 1`, where `Real.log 1 = 0` makes the
  right-hand side `0` and the literal statement false. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ A ∈ W, A.card = k) →
          (C * r * Real.log k) ^ k < (W.card : ℝ) →
            ∃ S ⊆ W, IsSunflower r S := by
  sorry

/-- Equivalent "sunflower function" phrasing.  If `sunflowerFree k r` collects the
families with no sunflower of `r` petals, then their size is at most
`(C r log k) ^ k`; i.e. `f(k, r) ≤ (C r log k) ^ k`. -/
theorem improved_sunflower_lemma_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ A ∈ W, A.card = k) →
          (¬ ∃ S ⊆ W, IsSunflower r S) →
            (W.card : ℝ) ≤ (C * r * Real.log k) ^ k := by
  sorry

end Agent093
