import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `petals` of sets is a **sunflower** with **core** `Y` when

* every set of the family contains `Y`, and
* any two distinct sets of the family meet exactly in `Y`.

Consequences (for `petals.card ≥ 2`): the "petals" `s \ Y` for `s ∈ petals` are pairwise
disjoint, and every element lying in at least two members of the family lies in `Y`, hence
in every member. Distinctness of the sets of the family is automatic because `petals` is a
`Finset`; "`r` petals" is expressed as `petals.card = r`. -/
def IsSunflower [DecidableEq α] (petals : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ s ∈ petals, Y ⊆ s) ∧
    (∀ s ∈ petals, ∀ t ∈ petals, s ≠ t → s ∩ t = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for all positive integers `k` and `r`, every
finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C · r · (log k + 1))^k`, contains a sunflower with `r` petals: an `r`-element
subfamily `S ⊆ W` that is a sunflower (`IsSunflower`) for some core `Y`.

Encoding notes.

* Sets are `Finset α` over an arbitrary ambient type `α`; the family is `W : Finset (Finset α)`.
  Because `C` is quantified *outside* `α`, it is genuinely absolute (independent of the
  ambient type).
* `Real.log` is the natural logarithm. The threshold uses `log k + 1` instead of `log k`
  so that it is meaningful and the statement is true for *every* positive `k`, including
  `k = 1` (where `log 1 = 0`, yet `r` distinct singletons already form a sunflower, so the
  bare `(C r log k)^k` bound would be false). For `k ≥ 2` one has `log k + 1 = Θ(log k)`,
  so this matches the asymptotic content `f(k, r) ≤ (C r log k)^k` of the theorem.
* `C` is existentially bound inside the theorem, together with `0 < C`.
* Cardinalities are `Finset.card`; the comparison with the real-valued threshold is done
  after coercing `W.card` to `ℝ`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * (Real.log (k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ S ⊆ W, ∃ Y : Finset α, S.card = r ∧ IsSunflower S Y := by
  sorry

end ImprovedSunflower
