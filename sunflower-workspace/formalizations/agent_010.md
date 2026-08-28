# Agent 010 — improved sunflower lemma, statement only

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧
  ∀ (k r : ℕ), 2 ≤ k → 0 < r →
    ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
        ∃ 𝒮 ⊆ W, ∃ Y : Finset α, IsSunflowerWith 𝒮 r Y
```

with the auxiliary definition

```
def IsSunflowerWith (𝒮 : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop :=
  𝒮.card = r ∧ ∀ ⦃s⦄, s ∈ 𝒮 → ∀ ⦃t⦄, t ∈ 𝒮 → s ≠ t → s ∩ t = Y
```

## Encoding decisions and why

- **Set representation:** `Finset (Finset α)` over an ambient `[DecidableEq α]` type
  (`α` is a section `variable`, so the theorem holds for every type). Finsets give
  `card` directly, make finiteness free, and make "distinct members" automatic — no
  separate injectivity/distinctness hypothesis is needed. `s ∩ t` and `s.card` are the
  usual `Finset` operations.
- **Sunflower predicate:** defined locally as `IsSunflowerWith 𝒮 r Y` = "`|𝒮| = r` and
  every pairwise intersection of distinct members equals `Y`". This is the
  "pairwise intersections all coincide" formulation together with an explicit core `Y`
  and an explicit petal count. Distinctness of the `r` sets is encoded by `𝒮.card = r`
  for a `Finset`. The sunflower is required to sit inside `W` via `𝒮 ⊆ W`; its members
  then automatically have cardinality `k`.
- **Petals nonempty:** not required. `S \ Y` pairwise disjoint follows from
  `S ∩ T = Y`; at most one member can equal the core, so this matches the standard
  definition. Noted rather than imposed.
- **Logarithm:** `Real.log` (natural log), applied to `(k : ℝ)`. The base is
  immaterial because it is absorbed into `C`. The bound `(C * r * Real.log k) ^ k` is a
  real number (`ℝ` to a `ℕ` power) compared against `(W.card : ℝ)`.
- **k = 0 / k = 1:** excluded by the hypothesis `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0` makes the RHS `0`, but `f(1, r) = r`, so the naive statement is
  false there; `k = 0` is degenerate. Restricting to `k ≥ 2` is the standard
  convention in the literature (ALWZ / Rao / BCW all state the bound for `k ≥ 2`).
  An alternative that keeps all positive `k` would replace `Real.log k` by
  `Real.log k + 1` (or `max 1 (Real.log k)`); I preferred fidelity to the usual
  statement.
- **The constant `C`:** existentially quantified *inside* the theorem
  (`∃ C, 0 < C ∧ …`). This makes the statement self-contained and is the strongest
  reading ("there is an absolute constant").
- **Strict inequality:** `(C * r * Real.log k) ^ k < (W.card : ℝ)`, i.e.
  `|W| > (C r log k)^k`, exactly as in the task statement; equivalently
  `f(k,r) ≤ (C r log k)^k`.
- **`r ≥ 1`:** kept as `0 < r` since `r` petals with `r = 0` is vacuous/degenerate.

## Uncertainties

- Mathlib does contain a sunflower development (roughly
  `Mathlib.Combinatorics.SetFamily.Sunflower`) with a predicate I believe is named
  `Finset.IsSunflower` and the classical Erdős–Ko–Rado sunflower bound. I did not rely
  on it: I am not fully certain of its exact name or argument order (`IsSunflower r 𝒮 t`
  vs `IsSunflower 𝒮 t` with a separate card hypothesis), so I use a local definition
  `IsSunflowerWith` to keep the file self-contained and unambiguous. If the Mathlib
  predicate is `Finset.IsSunflower (r) (𝒮) (t)`, the conclusion could be rewritten as
  `∃ 𝒮 ⊆ W, ∃ Y, Finset.IsSunflower r 𝒮 Y`.
- `import Mathlib` (blanket import) is used for `Real.log`; a minimal import set would
  be `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus `Mathlib.Data.Finset.Card`.
- `∃ 𝒮 ⊆ W, ∃ Y : Finset α, …` relies on the standard Mathlib binder-predicate
  notation `∃ x ⊆ s, p x` unfolding to `∃ x, x ⊆ s ∧ p x`; believed correct.
- The explicit casts `((r : ℝ))` and `Real.log (k : ℝ)` are written out to avoid any
  elaboration ambiguity with the `ℕ` variables.
