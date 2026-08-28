# agent_097 — improved sunflower lemma (statement only)

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    HasSunflower W r
```

with two auxiliary definitions, `IsSunflower` and `HasSunflower`.

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient `α : Type*` with
  `[DecidableEq α]`; a family is `Finset (Finset α)`. This gives `Finset.card`
  for both the family size and the uniform set size `k`, and makes `∩` and the
  subfamily relation `⊆` directly available. No separate finiteness hypothesis
  is needed.

- **Sunflower predicate.** Defined locally as
  `IsSunflower P Y := (P : Set (Finset α)).Pairwise (fun S T => S ∩ T = Y)`,
  i.e. an explicit core `Y` with all pairwise intersections of distinct members
  equal to `Y`. `Set.Pairwise` already builds in "distinct" (`S ≠ T`). The
  petal-disjointness and "element in ≥2 sets ⇒ in all" properties are
  consequences, noted in a docstring rather than posed as extra conjuncts.

- **"Sunflower with r petals".** `HasSunflower W r` = there is `P ⊆ W` with
  `P.card = r` and some core `Y` making `P` a sunflower. Using an exact
  `P.card = r` (rather than `≥ r`) is equivalent for the conclusion and is
  cleaner. Distinctness of the `r` petals is automatic from `P` being a
  `Finset` of that cardinality, so it is not separately stated.

- **Petals nonempty:** not required. The source statement only asks for pairwise
  disjoint petals, which allows the (at most one) member equal to the core.

- **Logarithm:** `Real.log` (natural log). The RHS `(C * r * Real.log k) ^ k`
  is real; `W.card` is cast to `ℝ` and the containment threshold is a strict
  `<`. The choice of log base is absorbed into `C`.

- **k = 0, 1 handling:** excluded via the hypothesis `2 ≤ k`, which keeps
  `Real.log k > 0` so the bound is meaningful. These cases are combinatorially
  trivial (`f(1,r) = r`, `f(0,r) ≤ 1`) and not the content of the theorem.
  `1 ≤ r` is assumed for the same "no degenerate input" reason.

- **The constant `C`:** existentially quantified, and placed *outside* the
  quantifier over `α`, `k`, `r`, so that it is a single absolute constant
  (not allowed to depend on the ambient type or the parameters). `0 < C` is
  included so the statement is not vacuously satisfiable by `C ≤ 0`.

## Uncertainties

- Mathlib may already provide a sunflower predicate (plausibly
  `Finset.IsSunflower` in `Mathlib/Combinatorics/SetFamily/Sunflower.lean`,
  possibly taking a `Set (Finset α)` and a `core`, alongside the classical
  Erdős–Rado bound). I could not verify the exact name/signature, so I defined
  a local `IsSunflower` to keep the file self-contained. If the Mathlib name
  exists and matches, this definition could be replaced by it.

- `import Mathlib` is used for convenience (self-contained but heavy); the only
  real dependencies are `Finset`, `Set.Pairwise`, and `Real.log`.

- Instance-implicit binders inside the `∀` (`∀ {α : Type*} [DecidableEq α] ...`)
  are valid Lean 4 term-level syntax; used here to keep `C` independent of `α`.
  Not machine-checked (no compiler available).
