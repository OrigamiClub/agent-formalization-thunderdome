import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the quantitative refinements of Rao and of
Bell–Chueluecha–Warnke.

This file contains the **statement only**.  The proof is left as `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- A finite family `T` of finite sets is a *sunflower with core `core`* if any two
**distinct** members of `T` intersect in exactly `core`.

Equivalently (as noted in the informal statement): every element that lies in at least two
members of `T` lies in all of them, and the "petals" `S \ core` for `S ∈ T` are pairwise
disjoint.

Encoding notes:
* Distinctness of the members is automatic, since they are elements of a `Finset`.
* `Set.Pairwise` on the coercion `(T : Set (Finset α))` only constrains distinct pairs, which
  is exactly what the sunflower condition requires (we do not assert `S ∩ S = core`).
* The number of petals of such a sunflower is `T.card`.
* We do not separately require the petals to be nonempty; when all members have a common
  cardinality `k` with `core.card < k` this is automatic. -/
def IsSunflower (T : Finset (Finset α)) (core : Finset α) : Prop :=
  (T : Set (Finset α)).Pairwise fun S₁ S₂ => S₁ ∩ S₂ = core

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that:
for every ambient type `α`, every `k ≥ 2`, every `r ≥ 1`, and every finite family `W` of
subsets of `α` each of cardinality exactly `k`, if

  `(C * r * Real.log k) ^ k < |W|`

then `W` contains a sunflower with `r` petals: there exist a core `core` and a subfamily
`T ⊆ W` with `T.card = r` such that `T` is a sunflower with core `core`.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * Real.log k) ^ k`.

Encoding decisions:
* `C` is existentially quantified **outside** the quantifier over `α`, `k`, `r`, `W`, so it
  is a genuine absolute constant.
* Sets are `Finset α` over an unconstrained ambient type `α` (universally quantified inside
  the statement, after `C`), families are `Finset (Finset α)`, cardinalities are
  `Finset.card`.
* The logarithm is `Real.log` (natural log); the threshold is compared in `ℝ` against the
  natural-number cardinality `|W|` via a coercion.
* We take `2 ≤ k`, which guarantees `Real.log k > 0`.  The cases `k ≤ 1` are degenerate
  (`Real.log k ≤ 0`, so the threshold collapses) and are treated separately in the
  literature; `r ≥ 1` is likewise assumed. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ (core : Finset α) (T : Finset (Finset α)),
              T ⊆ W ∧ T.card = r ∧ IsSunflower T core := by
  sorry

end ImprovedSunflower
