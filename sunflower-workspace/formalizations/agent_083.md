# Agent 083 - Improved sunflower lemma (statement only)

## Form chosen

A single existential over the absolute constant, then universal over everything else:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ T ⊆ W, T.card = r ∧ ∃ Y : Finset α, IsSunflower T Y
```

with a local

```
def IsSunflower (T : Finset (Finset α)) (Y : Finset α) : Prop :=
  (T : Set (Finset α)).Pairwise fun s₁ s₂ => s₁ ∩ s₂ = Y
```

## Encoding decisions and why

- **Set representation:** `Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]`. This is the representation Mathlib's own sunflower material
  uses, keeps everything finite without side finiteness hypotheses, and makes
  `card` unambiguous (`Finset.card`).
- **Sunflower predicate:** defined explicitly as "all pairwise intersections of
  distinct members coincide," via `Set.Pairwise` on the coerced family. This is
  the core-free phrasing but I still expose the core `Y` as an argument so the
  conclusion names it. For `|T| ≥ 2` this forces `Y ⊆ s` for each `s ∈ T` and
  pairwise-disjoint petals, matching the problem's parenthetical. I did not use a
  Mathlib predicate directly (see uncertainties) but the definition is meant to be
  defeq/equivalent to `Finset.IsSunflower`.
- **"Sunflower with r petals":** `∃ T ⊆ W, T.card = r ∧ ∃ Y, IsSunflower T Y`.
  Exact cardinality `r`, not `≥ r`. Distinctness of the `r` sets is automatic from
  `Finset` membership, so it need not be stated separately.
- **Petals nonempty:** not imposed. With uniform size `k` and distinct members,
  no petal can be empty anyway (a petal `s \ Y = ∅` would give `s ⊆ s'` with
  `|s| = |s'| = k`, i.e. `s = s'`), so adding the condition would be redundant.
- **Logarithm:** `Real.log` (natural log). The base is irrelevant to the
  statement since a base change is a constant factor absorbed into `C`.
- **k = 0 / k = 1 handling:** restricted to `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0` collapses the right-hand side to `0`, which would make the
  implication false (`f(1, r) = r`, so a family of fewer than `r` singletons has
  no `r`-petal sunflower). For `k = 0` only `∅` has cardinality `0` so any such
  `W` has `card ≤ 1` and the hypothesis `... < W.card` combined with a positive
  `C` term is degenerate. Excluding `k ≤ 1` is standard in statements of this
  lemma (the interesting content is `k ≥ 2`). An alternative faithful-for-all-k
  variant is to write `Real.log (k + 1)` instead of `Real.log k`; I preferred the
  literal `log k` with the `k ≥ 2` guard.
- **Constant C:** existentially quantified as the outermost binder, ahead of
  `∀ α k r`, so it is a true absolute constant (cannot depend on the ambient type
  or on `k`, `r`). Stated with `0 < C`.
- **Strict inequality:** `(C r log k)^k < |W|`, matching "`|W| >` ...". The
  `ℕ`-valued `W.card` is cast to `ℝ` to compare with the real right-hand side.

## Uncertainties

- Mathlib almost certainly has `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
  with a predicate `Finset.IsSunflower` (roughly
  `(𝒮 : Set (Finset α)).Pairwise fun a b => a ∩ b = t`) and the classical
  Erdős–Rado bound (something like `(r - 1) ^ k * k ! < 𝒮.card → ∃ sunflower`).
  I did not rely on the exact name/signature and instead defined `IsSunflower`
  locally; the local definition is intended to match. The improved
  (ALWZ/Rao/BCW) bound is, to my knowledge, not in Mathlib.
- `Real.log` is the correct identifier for the natural logarithm in Mathlib; the
  cast `(k : ℝ)` / `(r : ℝ)` from `ℕ` and `(W.card : ℝ)` are standard coercions.
- `∃ T ⊆ W, P` sugar desugars to `∃ T, T ⊆ W ∧ P` in Mathlib; used here.
- `import Mathlib` is used for convenience rather than a minimal import set.
- Placing `∀ (α : Type*) [DecidableEq α]` under an `∃ C : ℝ` is fine in Lean 4
  (the statement becomes universe-polymorphic); this is deliberate to keep `C`
  absolute.
