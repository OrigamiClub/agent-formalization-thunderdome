/-
Agent 070 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
positive integers `k` and `r`, every finite family `W` of `k`-element sets with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/
import Mathlib

namespace ImprovedSunflower

/-- A *sunflower with `r` petals* and *core* `Y`, living in an ambient type `α`:
a family `P` of exactly `r` finite sets (automatically distinct, being the elements
of a `Finset`) whose pairwise intersections are all equal to `Y`.

Facts that therefore do *not* need to be stated separately:
* the petals `S \ Y` for `S ∈ P` are pairwise disjoint;
* every element lying in two members of `P` lies in `Y`, hence (for `r ≥ 2`) in all
  members of `P`;
* for `r ≥ 2` the core is contained in every petal: `Y ⊆ S` for all `S ∈ P`.

No nonemptiness of the petals or of the core is imposed. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (P : Finset (Finset α)) : Prop :=
  P.card = r ∧ ∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and
by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all positive integers `k` and
`r`, every finite family `W` of sets each of cardinality exactly `k`, with
`|W| > (C · r · log (k + 1))^k`, contains a sunflower with `r` petals.

Encoding decisions:
* Sets are `Finset`s over an arbitrary ambient type `α` with decidable equality;
  the family is `W : Finset (Finset α)`, so its members are automatically distinct
  and it is automatically finite.
* `C` is existentially quantified ("absolute constant"): a single `C` works for
  every ambient type `α`, every `k`, `r`, and `W`.
* The logarithm is the natural logarithm `Real.log`, applied to `k + 1` rather than
  `k`. This keeps the statement correct in the degenerate case `k = 1`, where
  `Real.log k = 0` would make the right-hand side vacuously `0`; replacing `log k`
  by `log (k + 1)` only changes the implied constant, which is already existentially
  quantified.
* The size comparison is carried out in `ℝ` (`W.card` and `r` are coerced).
* "Contains a sunflower with `r` petals" is `∃ Y P, P ⊆ W ∧ IsSunflower r Y P`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        0 < k → 0 < r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end ImprovedSunflower
