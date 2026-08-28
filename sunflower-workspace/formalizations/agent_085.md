# agent_085 — improved sunflower lemma (statement)

## Form chosen

A single existential over an absolute constant `C > 0`, then universal over the
ambient type, `k`, `r`, and the family `W`:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
    2 ≤ k → 1 ≤ r →
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ S ⊆ W, S.card = r ∧ ∃ Y, IsSunflower S Y
```

This is the "family / threshold" form: if the family is larger than the bound it must
contain a sunflower, which is equivalent to `f(k,r) ≤ (C r log k)^k` for the sunflower
function `f`. I did not also state the `f(k,r) ≤ …` version, since defining `f`
(an `sInf` over "no sunflower" families) adds machinery without adding content.

## Encoding decisions

- **Set representation**: `Finset α` for individual sets over an ambient type `α` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This gives finiteness,
  cardinalities via `Finset.card`, and automatic distinctness of members for free.
- **Sunflower predicate**: defined locally as `IsSunflower S Y`, the "explicit core"
  formulation: `∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁ ∩ s₂ = Y`. This matches the task's
  wording ("a core set `Y` with `S_i ∩ S_j = Y` for every `i ≠ j`") exactly. Petals
  are not required nonempty; `Y` is not separately constrained to be `⊆ s` (it follows
  automatically once `r ≥ 2`). Number of petals is `S.card`, pinned with `S.card = r`.
- **Mathlib predicate**: Mathlib has `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
  with a `Finset.IsSunflower` / `IsSunflower`-style predicate and the classical
  Erdős–Rado bound, but I did not rely on the exact name to keep the file
  self-contained and robust; the local definition is deliberately close to what I
  recall Mathlib uses (`Set.Pairwise` on the family with intersection `= core`).
- **Logarithm**: `Real.log` (natural log). The whole size comparison is cast to `ℝ`.
  Base is immaterial to the statement since it is absorbed into `C`; natural log is the
  usual convention in the ALWZ/Rao papers.
- **`k = 0` / `k = 1`**: handled by assuming `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`
  makes the RHS `0`, so the hypothesis would be `|W| > 0`, which does not imply an
  `r`-petal sunflower; for `k = 0` the sets are all empty. `k ≥ 2` is the standard
  domain where `(C r log k)^k` is meaningful.
- **`r`**: assumed `1 ≤ r`. `r = 1` is a degenerate ("trivial") sunflower and the
  predicate is vacuously satisfied; the interesting range is `r ≥ 2` or `r ≥ 3`, but
  the stated form is correct for all `r ≥ 1`.
- **`C`**: existentially quantified as `∃ C : ℝ, 0 < C ∧ …`, outermost, so it is a
  genuine absolute constant independent of `α, k, r, W`.
- **Strictness**: hypothesis is strict, `bound < |W|`, matching "`|W| > (C r log k)^k`".
- **Distinctness of members**: not stated explicitly; free from `S : Finset (Finset α)`
  with `S ⊆ W`.

## Uncertainties

- Whether `import Mathlib` plus the local `IsSunflower` avoids any name clash with a
  global `IsSunflower` in current Mathlib — placed inside `namespace ImprovedSunflower`
  to be safe, so references are `ImprovedSunflower.IsSunflower`.
- Exact Mathlib identifier for its own sunflower predicate/lemma (`Finset.IsSunflower`,
  `Finset.exists_isSunflower`, …) is from memory and not used here.
- Coercions: `Real.log (k : ℝ)` and `(r : ℝ)`, `(W.card : ℝ)` written explicitly; the
  `^ k` is `Monoid.npow` with `k : ℕ`, which is the intended real power here.
- Allowing instance binder `[DecidableEq α]` inside the `∀` after an explicit `(α : Type*)`
  is legal Lean 4 term syntax; I used explicit `α` rather than implicit to keep parsing
  unambiguous.
