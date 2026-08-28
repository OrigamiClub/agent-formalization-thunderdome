/-
Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): statement only.

There is an absolute constant `C` such that for all `k, r` every finite family of
`k`-element sets of cardinality `> (C · r · log k)^k` contains a sunflower with
`r` petals.

Self-contained: the sunflower vocabulary is defined here rather than relying on
Mathlib's `Mathlib.Combinatorics.SetFamily.Sunflower` (which, as of the knowledge
cutoff, only carries the classical Erdős–Rado bound).
-/
import Mathlib

open Finset

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower r Y P` : the finite family `P` is a *sunflower with `r` petals and
core `Y`*, i.e. `P` consists of exactly `r` (automatically distinct, since `P` is a
`Finset`) sets, and the intersection of any two distinct members equals `Y`.

Consequences (not part of the definition): every element lying in `≥ 2` members
lies in all of them; the petals `s \ Y` for `s ∈ P` are pairwise disjoint; and
when `2 ≤ r` and all members have equal cardinality the petals are nonempty. -/
def IsSunflower (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃s₁ : Finset α⦄, s₁ ∈ P → ∀ ⦃s₂ : Finset α⦄, s₂ ∈ P → s₁ ≠ s₂ → s₁ ∩ s₂ = Y

/-- A family `W` *contains a sunflower with `r` petals* when some subfamily of `W`
is a sunflower with `r` petals (with respect to some core `Y`). -/
def ContainsSunflower (r : ℕ) (W : Finset (Finset α)) : Prop :=
  ∃ Y : Finset α, ∃ P ⊆ W, IsSunflower r Y P

/-- **Improved sunflower lemma.**  There is an absolute constant `C > 0` such that
for every type `α`, all `k ≥ 2` and `r ≥ 1`, and every finite family `W` of
`k`-element subsets of `α`, if `|W| > (C · r · log k)^k` then `W` contains a
sunflower with `r` petals.

Encoding notes:
* `C` is existentially quantified *outside* the `∀ α`, so it is genuinely
  absolute (independent of the ambient type, `k` and `r`).
* Logarithm: `Real.log` (natural log); the bound is compared in `ℝ` against the
  natural-number cardinality `W.card`.
* `k ≥ 2` is assumed: for `k ≤ 1` the term `Real.log k ≤ 0` collapses the bound to
  `0` and the statement fails (e.g. `k = 1`, `r = 3`, a single singleton). The
  `k ≤ 1` cases are trivial/degenerate and handled separately.
* Sets of size exactly `k` via `Finset.card`; distinctness of the sunflower
  members is automatic from `P : Finset (Finset α)` together with `P.card = r`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ContainsSunflower r W := by
  sorry

/-- Equivalent "sunflower function" phrasing: if `f k r` bounds the size of the
largest sunflower-free family of `k`-sets (families with `f k r` or fewer members
need not contain an `r`-petal sunflower, families with more always do), then
`f k r ≤ (C · r · log k)^k`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      (∀ s ∈ W, s.card = k) → f k r < W.card → ContainsSunflower r W) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 2 ≤ k → 1 ≤ r →
      (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
