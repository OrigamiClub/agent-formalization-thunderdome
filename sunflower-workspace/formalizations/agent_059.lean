import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), *Improved bounds for the sunflower lemma*, with the
subsequent refinements by Rao and by Bell–Chueluecha–Warnke.

Only the *statement* is formalized here; the proof is `sorry`.
-/

namespace ImprovedSunflower

open Finset

variable {α : Type*}

/-- A *sunflower with `r` petals and core `Y`* sitting inside a set family `W`:
a subfamily `P ⊆ W` consisting of exactly `r` (necessarily distinct, since `P` is a
`Finset`) sets, any two distinct members of which meet exactly in `Y`.

For `r ≥ 2` the condition `S ∩ T = Y` forces `Y ⊆ S` for every `S ∈ P`, hence every
element lying in at least two members lies in `Y` and therefore in all of them, and the
petals `S \ Y` (`S ∈ P`) are pairwise disjoint — matching the usual informal
definition. -/
def IsSunflower [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  P ⊆ W ∧ P.card = r ∧
    ∀ ⦃S : Finset α⦄, S ∈ P → ∀ ⦃T : Finset α⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- `W` contains a sunflower with `r` petals (with some core). -/
def HasSunflowerWith [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ (P : Finset (Finset α)) (Y : Finset α), IsSunflower W r P Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`,
and every finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

`log` is the natural logarithm (`Real.log`); the choice of base only rescales `C`.
The type `α` and the family `W` are quantified *inside* the existential for `C`, so that
`C` is genuinely absolute.  The hypothesis `2 ≤ k` excludes the degenerate cases
`k = 0` (then `W` has at most one member) and `k = 1` (then `log k = 0`, and
`f(1, r) = r` is immediate). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflowerWith W r := by
  sorry

end ImprovedSunflower
