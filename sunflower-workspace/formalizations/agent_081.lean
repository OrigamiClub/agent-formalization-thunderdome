import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the subsequent refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains the *statement* only.  The single theorem is closed with
`sorry`; nothing is proved.

## Encoding summary

* Sets are `Finset α` over an ambient type `α` with `DecidableEq α`; a family of
  sets is a `Finset (Finset α)`.  Distinctness of members is then automatic.
* A sunflower is encoded by an explicit core `Y : Finset α` together with the
  condition that any two distinct members meet exactly in `Y`
  (`IsSunflower` below).
* "Sunflower with `r` petals" means: an `r`-element subfamily that is a sunflower
  for some core (`HasSunflower` below).  `r` is the number of petals /
  cardinality of the subfamily.
* The logarithm is `Real.log` applied to the real coercion of `k`.  Because
  `Real.log 1 = 0` makes the bound vacuously `0` (and `Real.log` is negative for
  `k = 0`), the statement is restricted to `2 ≤ k`, which is the range in which
  the bound is meaningful.
* `C` is existentially quantified *outside* the quantifier over the ambient type
  `α`, `k`, `r`, and `W`, so it is a genuine absolute constant.  An explicit
  `universe u` is used so that `α` can be universally quantified inside the
  existential.
* Cardinalities are `Finset.card`.  The size hypothesis is the strict inequality
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` in `ℝ`.
-/

universe u

/-- A finite family `P` of finite sets is a **sunflower with core `Y`** if every
two distinct members of `P` intersect in exactly `Y`.

Consequences (not part of the definition): if `2 ≤ P.card` then `Y ⊆ s` for every
`s ∈ P`, every element lying in two members lies in all members, and the petals
`s \ Y` for `s ∈ P` are pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = Y

/-- The family `W` **contains a sunflower with `r` petals**: there is an
`r`-element subfamily `P ⊆ W` and a core `Y` making `P` a sunflower. -/
def HasSunflower {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ (P : Finset (Finset α)) (Y : Finset α),
    P ⊆ W ∧ P.card = r ∧ IsSunflower P Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; Rao;
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type u} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            HasSunflower W r := by
  sorry
