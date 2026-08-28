# Agent 030 — improved sunflower lemma, statement only

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ {α} [DecidableEq α] (W : Finset (Finset α)),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ (S : Finset (Finset α)) (Y : Finset α), S ⊆ W ∧ S.card = r ∧ IsSunflower S Y
```

plus one auxiliary definition `IsSunflower`.

## Encoding decisions and why

- **Set representation.** Members are `Finset α` over an arbitrary ambient type
  `α` with `[DecidableEq α]` (needed for `∩`). The family `W` is
  `Finset (Finset α)`. Benefits: finiteness of `W` and of each member is free;
  the members of `W` and of `S` are automatically distinct, so distinctness of
  the sunflower's `r` sets is captured by `S.card = r` with nothing extra to
  state.
- **Sunflower predicate.** Defined explicitly as: all pairwise intersections of
  distinct members equal a common core `Y`
  (`∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y`). This is definitionally the
  `Set.Pairwise` form `(↑S : Set _).Pairwise (fun s t => s ∩ t = Y)`. I inlined
  it rather than relying on a Mathlib predicate — see uncertainties. The core `Y`
  is existentially quantified in the conclusion ("there is a core set `Y`").
- **Number of petals.** `S.card = r` (exact count), `S ⊆ W`. Petals `s \ Y` are
  not separately constrained: for `r ≥ 2`, distinct members with equal pairwise
  intersection `Y` automatically have nonempty, pairwise-disjoint petals. The
  "every element in ≥ 2 sets is in all of them" / "petals disjoint" clauses are
  consequences of the pairwise-intersection definition, so not stated.
- **The constant `C`.** Existentially quantified, and placed *outside* the
  quantifiers over `α, k, r, W`, so it is a genuine absolute constant. `0 < C`
  recorded. Contrapositive reading: `f(k,r) ≤ (C r log k)^k`.
- **Logarithm.** `Real.log`. The bound inequality lives in `ℝ`; `k`, `r`, and
  `W.card` are cast from `ℕ`. `^ k` is the natural-number monoid power.
- **`k = 0, 1` handling.** Excluded via hypothesis `2 ≤ k`, so `Real.log k > 0`
  and the RHS is a positive real. With `Real.log`, `k = 1` gives RHS `= 0` and
  the strict-inequality statement becomes false (`k = 1, r = 2`: two singletons
  always form a 2-sunflower, but `|W| > 0` does not give `|W| ≥ 2`). A fully
  general alternative keeps `1 ≤ k` and uses `(C * r * (1 + Real.log k)) ^ k`;
  I preferred the literal `(C r log k)^k` from the task text with `k ≥ 2`.
- **`r`.** `1 ≤ r` ("positive integer `r`"). `r = 1` case is degenerate but
  harmless (`IsSunflower` on a singleton family holds for any `Y`).

## Uncertainties

- Mathlib *does* contain the classical Erdős–Rado sunflower lemma (bound
  `(r-1)^k · k!`), I believe with a predicate named `Finset.IsSunflower` (or in a
  `Sunflower` namespace) and a lemma like `Finset.exists_sunflower`. I did not
  rely on these because (a) I could not verify the exact identifiers without a
  compiler, and (b) the *improved* (ALWZ) bound is not in Mathlib. My local
  `IsSunflower` is self-contained; if it clashes with a Mathlib name, it is
  namespaced under `ImprovedSunflower`.
- `import Mathlib` is used for `Real.log` and `Finset` API; a minimal import set
  would be `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus
  `Mathlib.Data.Finset.Card` (not verified).
- Binder syntax: implicit `{α : Type*} [DecidableEq α]` appearing after several
  `→`-hypotheses inside the statement is valid Lean 4, but not machine-checked
  here.
- Whether to also assert `Y ⊆ s` for each `s ∈ S`: omitted; implied for `r ≥ 2`.
