import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with subsequent refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains the *statement only*.  Every theorem ends with `:= by sorry`
and nothing is proved.
-/

namespace Agent031

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower P r Y` says that the finite family of sets `P` is a
*sunflower with `r` petals* and *core* `Y`:

* `P` consists of exactly `r` sets (they are automatically distinct, being the
  elements of a `Finset`), and
* any two distinct members of `P` intersect in exactly the core `Y`.

Standard consequences, which are therefore *not* imposed as part of the
definition:

* for `r ≥ 2`, `Y ⊆ A` for every `A ∈ P` (take `Y = A ∩ B` for some `B ≠ A`);
* the petals `A \ Y`, for `A ∈ P`, are pairwise disjoint;
* any element lying in two members of `P` lies in `Y`, hence in all of them.

Petals are allowed to be empty (the classical Erdős–Rado convention). -/
structure IsSunflower (P : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop where
  /-- The sunflower has exactly `r` petals. -/
  card_petals : P.card = r
  /-- Any two distinct members meet exactly in the core `Y`. -/
  inter_eq_core : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k`
and `r`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C * r * log (k + 1)) ^ k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C * r * log (k+1))^k`.

Encoding choices:

* **Sets.** A set is a `Finset α` for a fixed ambient type `α` with decidable
  equality; the family `W` is a `Finset (Finset α)`.  No `Infinite α` hypothesis
  is needed for the statement to be true (for small finite `α` the cardinality
  hypothesis simply becomes unsatisfiable).
* **Distinctness.** Members of `W`, and of the sunflower `P`, are distinct
  automatically because these are `Finset`s; `IsSunflower.card_petals` pins the
  number of petals to exactly `r`.
* **Logarithm.** `log` is the natural logarithm `Real.log`.  We take
  `Real.log ((k : ℝ) + 1)` rather than `Real.log k`; since `Real.log 1 = 0`,
  using `Real.log k` would make the bound vacuously `0` at `k = 1` and the
  statement false there.  For `k ≥ 2`, `log (k+1) = Θ(log k)`, so this only
  rescales the absolute constant `C`.  (Any fixed base of logarithm works, the
  base being absorbed into `C`.)
* **The constant `C`.** Existentially quantified inside the statement, together
  with `0 < C`.
* **Cardinality comparison.** `Finset.card`, cast into `ℝ`, compared strictly
  (`<`) against the real-valued bound, matching `|W| > (C r log(k+1))^k`.
* **Sunflower location.** The conclusion asserts `P ⊆ W` with `IsSunflower P r Y`
  for some core `Y`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 1 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ (P : Finset (Finset α)) (Y : Finset α),
            P ⊆ W ∧ IsSunflower P r Y := by
  sorry

end Agent031
