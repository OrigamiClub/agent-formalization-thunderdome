import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), sharpened by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the theorem ends with `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `P` of finsets is a *sunflower with core `Y`* when any two distinct
members of `P` intersect exactly in `Y`.

Equivalently: every point lying in at least two members of `P` lies in all of them, and the
petals `s \ Y` (for `s ∈ P`) are pairwise disjoint.  We do **not** require the petals to be
nonempty.

Mathlib very likely already contains this notion (file
`Mathlib.Combinatorics.SetFamily.Sunflower`, plausibly under a name such as
`Finset.IsSunflower`, possibly bundling the petal count `r`).  To keep this statement
independent of the exact spelling we give a small self-contained definition. -/
def IsSunflower {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  (↑P : Set (Finset α)).Pairwise (fun s t => s ∩ t = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k` and `r`, every
finite family `W` of finsets, each of cardinality exactly `k`, with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals: `r` distinct members of `W`
whose pairwise intersections all coincide (with some common core `Y`).

Encoding notes:
* Sets are `Finset α` over an ambient type; the family is `W : Finset (Finset α)`.
* `log` is the natural logarithm `Real.log`.  Since `Real.log 1 = 0` and `Real.log 0 = 0`,
  the raw bound `(C r log k)^k` would be false for `k = 1`; we therefore use
  `max (Real.log k) 1`, which agrees with `log k` for all large `k` and keeps the statement
  true (and nonvacuous) for every `k ≥ 1`.
* `C` is existentially quantified: "there is an absolute constant".
* The number of petals is `P.card = r`; because `P : Finset (Finset α)`, this also records
  that the `r` chosen sets are pairwise distinct.
* Petals are not required to be nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        1 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * max (Real.log (k : ℝ)) 1) ^ k < (W.card : ℝ) →
        ∃ (P : Finset (Finset α)) (Y : Finset α),
          P ⊆ W ∧ P.card = r ∧ IsSunflower P Y := by
  sorry

/-- Reformulation in terms of the sunflower function `f k r`, the least cardinality that
forces a sunflower with `r` petals among `k`-sets: `f k r ≤ (C · r · log k)^k`.

Here `f` is supplied abstractly by its defining property (any family of `k`-sets of size
`≥ f k r` contains an `r`-petal sunflower), which is why it appears as a hypothesis. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      (∀ s ∈ W, s.card = k) → f k r ≤ W.card →
      ∃ (P : Finset (Finset α)) (Y : Finset α), P ⊆ W ∧ P.card = r ∧ IsSunflower P Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 1 ≤ k → 1 ≤ r →
      (f k r : ℝ) ≤ (C * (r : ℝ) * max (Real.log (k : ℝ)) 1) ^ k := by
  sorry

end ImprovedSunflower
