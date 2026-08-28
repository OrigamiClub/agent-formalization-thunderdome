# Agent 047 — improved sunflower lemma, statement only

## Form chosen

Two `theorem ... := by sorry` statements in namespace `ImprovedSunflower`:

1. `improved_sunflower_lemma` — the containment form: `∃ C > 0`, for all `k ≥ 2`,
   `r ≥ 1`, every finite family `W` of exactly-`k`-sets with `|W| > (C·r·log k)^k`
   has a subfamily that is a sunflower with `r` petals.
2. `improved_sunflower_lemma_function` — the same bound restated for a sunflower
   function `f k r`, supplied as a parameter together with a hypothesis `hf`
   characterising it as `IsGreatest` of the set of sizes of sunflower-free families.
   Provided because the task mentions the "`f(k,r) ≤ (C r log k)^k`" phrasing; the
   first theorem is the primary deliverable.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for the
  family `W`, with `variable {α : Type*} [DecidableEq α]`. This matches Mathlib's
  existing `Mathlib.Combinatorics.SetFamily.Sunflower`. No finiteness side hypotheses
  needed. The statement is a genuine (non-vacuous) instance for any `α` large enough
  to hold `k`-sets, e.g. `α := ℕ`; it stays true (vacuously or not) for finite `α`.
- **Sunflower predicate.** Defined locally as `IsSunflower r Y P` :=
  `P.card = r ∧ (∀ S ∈ P, Y ⊆ S) ∧ (∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y)`.
  Explicit core `Y`. "r distinct sets" is captured by `P.card = r` (elements of a
  `Finset` are distinct by construction), so distinctness need not be stated
  separately. `Y ⊆ S` is included so the core is meaningful even for `r ≤ 1`
  (for `r ≥ 2` it follows from the intersection condition). Petals `S \ Y` are not
  required nonempty — the standard convention.
- **Logarithm.** `Real.log` (natural log), Mathlib's default. The log base only
  rescales the existential constant `C`, so the choice is immaterial to the statement.
- **k = 0, 1.** Excluded by the hypothesis `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`
  makes the RHS `0`, and the resulting claim is false (a family of many singletons is
  a union of 1-petal sunflowers only); for `k = 0` the RHS is `1` and the hypothesis
  is unsatisfiable. `k = 1` is elementary and not the content of the theorem.
- **Constant `C`.** Existentially quantified inside the theorem, `0 < C`.
- **Cardinality.** `Finset.card` throughout (`S.card`, `W.card`, `P.card`).
- **Strict bound.** Hypothesis `(C·r·log k)^k < (W.card : ℝ)`, i.e. `|W| >` the bound,
  as stated in the task.
- **Coercions.** Written explicitly: `(r : ℝ)`, `Real.log (k : ℝ)`, `(W.card : ℝ)`.

## Uncertainties

- Mathlib does have `Mathlib.Combinatorics.SetFamily.Sunflower` with an `IsSunflower`
  notion and the classical Erdős–Rado bound, but I could not verify the exact current
  signature (argument order, whether it fixes the petal count `r`, whether it is
  stated for `Finset` or `Set`). To stay self-contained and unambiguous I defined my
  own `IsSunflower`; a reviewer may wish to replace it with the library predicate.
- `import Mathlib` (whole library) is used for convenience; the only real dependency
  is `Real.log` plus `Finset`/`IsGreatest` basics.
- In `improved_sunflower_lemma_function`, `f` and its characterisation `hf` are taken
  as parameters rather than constructing `f` via `sSup`/`Nat.find`; this keeps the
  statement short and unambiguous. The `IsGreatest` set-builder is my own phrasing,
  not a known Mathlib identifier.
- Not required to hold: `[Infinite α]`. Adding it would rule out vacuous finite-`α`
  readings but is not needed for correctness.
