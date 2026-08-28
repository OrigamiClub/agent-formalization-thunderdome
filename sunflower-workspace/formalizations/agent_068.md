# Agent 068 — Improved sunflower lemma (statement only)

## Form chosen

A single self-contained `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
  2 ≤ k → 1 ≤ r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ P ⊆ W, IsSunflower P r
```

plus two auxiliary defs `IsSunflowerWith` (core made explicit) and `IsSunflower`
(core existentially quantified).

## Encoding decisions

* **Set representation.** `Finset (Finset α)` over an arbitrary ambient type `α`
  with `[DecidableEq α]`. This is the representation Mathlib itself uses for
  set-family combinatorics (Kruskal–Katona, the classical sunflower file), keeps
  everything finite without carrying `Set.Finite` hypotheses, and makes
  `Finset.card` the obvious notion of size.

* **Sunflower definition.** Defined locally as: `P.card = r` together with
  `∀ S T ∈ P, S ≠ T → S ∩ T = Y`. The "pairwise intersection equals the core"
  formulation is equivalent to the "every element in ≥ 2 sets is in all of them
  / petals pairwise disjoint" description and is the cleaner one to state. I did
  not depend on Mathlib's predicate — see uncertainties.

* **`r` petals / distinctness.** Encoded by `P.card = r` on a `Finset`; elements
  of a `Finset` are automatically distinct, so no separate injectivity clause is
  needed.

* **Empty petals.** Allowed: a member of `P` may equal `Y`. This matches the
  standard statement (the sunflower function counts sets, not nonempty petals).

* **Logarithm.** `Real.log` (natural log). Since the constant `C` is absolute and
  existentially quantified, the choice of log base only changes `C`, so `Real.log`
  vs `Real.logb 2` are interchangeable here.

* **`k = 1` / `k = 0`.** Guarded away with hypothesis `2 ≤ k`, so that
  `Real.log k > 0` and the bound is meaningful. For `k = 1` (a family of
  singletons) the correct statement is the trivial `|W| ≥ r`, which is a
  different bound and not an instance of `(C r log k)^k`; folding it in would
  require e.g. `Real.log (k+1)` or `max 1 (Real.log k)` and a larger `C`. I chose
  the textbook "`k ≥ 2`" phrasing for faithfulness/cleanliness. `k = 0` is
  excluded a fortiori (also "positive integers" in the problem statement).

* **`r`.** Kept fully general with `1 ≤ r` ("all positive integers `r`"), even
  though the bound is only interesting for larger `r`.

* **Constant `C`.** Existentially quantified at top level, before `α`, `k`, `r`,
  `W`, so it is genuinely absolute (cannot depend on any of them). `0 < C` is
  included so it cannot be trivially satisfied by `C = 0`.

* **Cardinality comparison.** Strict `<` matching "`|W| > (C r log k)^k`", with
  `W.card` coerced to `ℝ` since the right side is real. Base real, exponent
  `k : ℕ` (`Monoid.npow`).

* **Conclusion.** `∃ P ⊆ W, IsSunflower P r`, i.e. `∃ P, P ⊆ W ∧ ∃ Y, ...`.
  Membership `P ⊆ W` forces every set of the sunflower to have cardinality `k`,
  so that is not restated.

## Uncertainties

* **Mathlib sunflower predicate.** Mathlib has
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with (as I recall) a
  predicate along the lines of
  `Finset.IsSunflower (r : ℕ) (t : Finset α) (𝒮 : Finset (Finset α))` defined as
  `𝒮.card = r ∧ (𝒮 : Set _).Pairwise (fun s t => s ∩ t = t_core)`, plus the
  classical Erdős–Rado bound (`(r-1)^k * k! < 𝒮.card`). I was not confident
  enough of the exact name / argument order to use it, so I inlined an
  equivalent local definition. If the Mathlib name is stable, `IsSunflower P r`
  could be replaced by `∃ Y, Finset.IsSunflower r Y P` (argument order to be
  checked).

* **Binder in existential.** `∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [DecidableEq α] ...`
  puts a universe-polymorphic `∀` and an instance binder under an `∃`. This is
  well-formed (`Prop` is impredicative) and elaborates in Mathlib, but if it
  causes trouble the alternative is to make `C` a section variable / hypothesis
  `(C : ℝ) (hC : 0 < C) (hC' : <the sunflower property holds for C>)` or to state
  it as a `def sunflowerBound` plus a theorem.

* **Coercions.** `Real.log (k : ℝ)` and `(r : ℝ)` written explicitly to avoid
  relying on automatic `ℕ → ℝ` insertion inside the product.
