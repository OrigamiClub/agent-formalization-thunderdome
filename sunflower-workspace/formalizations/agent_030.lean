/-
Improved sunflower lemma — STATEMENT ONLY.

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke:
there is an absolute constant `C` such that every finite family of `k`-element
sets of size greater than `(C · r · log k)^k` contains a sunflower with `r`
petals.

Agent 030, independent formalization diversity study. No proof is given.
-/
import Mathlib

namespace ImprovedSunflower

open scoped Nat

variable {α : Type*}

/-- A **sunflower with core `Y`**: a finite family `S` of finite sets whose
pairwise intersections all equal `Y`.

The number of *petals* is `S.card`; the petals themselves are the sets `s \ Y`
for `s ∈ S`. From this predicate one recovers the usual informal description:
every element lying in two members of `S` lies in `Y` (hence in all members that
contain `Y`), and the petals `s \ Y` are pairwise disjoint.

This is defeq to `(↑S : Set (Finset α)).Pairwise (fun s t => s ∩ t = Y)`. We
spell it out to keep the file self-contained and unambiguous. -/
def IsSunflower [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s : Finset α⦄, s ∈ S → ∀ ⦃t : Finset α⦄, t ∈ S → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and
by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, and every finite family `W` of sets each of cardinality exactly `k`, if

  `(C · r · log k) ^ k  <  |W|`

then `W` has an `r`-element subfamily `S` that is a sunflower (with some core
`Y`). Equivalently, the sunflower function satisfies `f(k, r) ≤ (C r log k)^k`.

Encoding notes:
* Sets are `Finset α` for an arbitrary ambient type `α`; the family `W` is a
  `Finset (Finset α)`, so its members are automatically distinct and finite, and
  `S.card = r` already encodes "`r` distinct sets".
* `C` is existentially quantified *outside* the quantifier over `α`, `k`, `r`,
  `W`, so it is genuinely absolute (independent of all of them).
* `log` is `Real.log`. The inequality is stated in `ℝ` with `|W|` and the
  positive integers `k`, `r` coerced from `ℕ`.
* `k ≥ 2` is assumed so that `Real.log k > 0` and the bound is non-degenerate;
  the cases `k ∈ {0, 1}` are excluded (there `Real.log k = 0`, which would make
  the literal statement false, e.g. `k = 1, r = 2`). A variant valid for all
  `k ≥ 1` replaces `Real.log k` by `1 + Real.log k`.
* Petals need not be required nonempty: for `r ≥ 2`, distinctness of the members
  of `S` already forces each `s \ Y` to be nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (S : Finset (Finset α)) (Y : Finset α),
            S ⊆ W ∧ S.card = r ∧ IsSunflower S Y := by
  sorry

end ImprovedSunflower
