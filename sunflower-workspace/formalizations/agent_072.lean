import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

there is an absolute constant `C` such that for all `k, r`, every finite family of
`k`-element sets of size greater than `(C · r · log k) ^ k` contains a sunflower
with `r` petals.

Only the statement is given; the proof is `sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `P` of finite sets is a **sunflower with core `Y`** when any two
distinct members meet in exactly `Y`.

The *petals* are the sets `s \ Y` for `s ∈ P`.  This condition forces the petals to be
pairwise disjoint and forces every element that lies in two members to lie in all of
them, which is the usual informal description of a sunflower. -/
def IsSunflower {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → s ∩ t = Y

/-- `P` is a **sunflower with `r` petals** if it has exactly `r` members and admits some
core `Y`.  Members of a `Finset` are automatically pairwise distinct, so this really is a
family of `r` distinct sets. -/
def IsSunflowerWith {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (r : ℕ) : Prop :=
  P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang 2019; bound refined by Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every integer `k ≥ 2`, every integer
`r ≥ 1`, every type `α`, and every finite family `W` of `k`-element subsets of `α` with
`(C * r * Real.log k) ^ k < W.card`, the family `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * Real.log k) ^ k`.

The single constant `C` is required to work uniformly over all ambient types `α`, so the
quantifier over `α` sits *inside* the existential over `C`.

The hypothesis `2 ≤ k` removes the degenerate cases `k = 0` and `k = 1`: there
`Real.log k = 0`, which would make the right-hand side collapse to `0` and the statement
false.  See `agent_072.md` for alternative treatments of small `k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ P : Finset (Finset α), P ⊆ W ∧ IsSunflowerWith P r := by
  sorry

end ImprovedSunflower
