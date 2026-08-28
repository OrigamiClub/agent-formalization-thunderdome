# agent_041 — improved sunflower lemma (statement only)

## Form chosen

A single existential over the absolute constant `C`, wrapping a universally
quantified statement:

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ P : Finset (Finset α), P ⊆ W ∧ IsSunflower r P
```

with an auxiliary predicate `IsSunflower r P`.

## Encoding decisions and rationale

- **Set representation:** `Finset α` over an arbitrary ambient type `α`, family
  as `Finset (Finset α)`. Finsets give a clean `Finset.card` and make the family
  automatically finite with no side hypothesis. `[DecidableEq α]` is needed for
  `Finset` intersection `s ∩ t`.
- **`α` inside the quantifier prefix:** placed after `∃ C` so that `C` is
  manifestly independent of the ambient type. `Type*` becomes a universe
  parameter of the theorem.
- **Sunflower definition:** the Alweiss–Lovett–Wu–Zhang Definition 1.1 form —
  "all pairwise intersections of distinct members coincide", with the common
  value named as an explicit core `Y`. Bundled with `P.card = r` so the `r`
  petals are distinct. Did **not** additionally require `Y ⊆ s` for members or
  nonempty petals: for `r ≥ 2` core-containment is already implied, and empty
  petals are permitted by the standard convention (at most one petal is empty).
- **Subfamily returned as `P ⊆ W`** (a sub-`Finset`), rather than an indexed
  family; distinctness is then free.
- **Logarithm:** `Real.log` (natural log). Base is irrelevant, absorbed into `C`.
- **`k = 1` / `k = 0`:** excluded via `2 ≤ k`. At `k = 1`, `Real.log 1 = 0` makes
  the RHS `0`, and `|W| > 0` does not force a sunflower (`f(1,r) = r`), so the
  bound is genuinely false there; restricting to `k ≥ 2` is the faithful fix.
- **`r`:** `1 ≤ r` (for `r = 1` the conclusion is trivial; kept for uniformity).
- **Cardinality:** `Finset.card`, compared in `ℝ` via coercion of `W.card`.
- **`C`:** existentially quantified inside the theorem (not a hypothesis, not a
  named constant), with positivity `0 < C`.

## Uncertainties / guessed identifiers

- `Real.log` — high confidence this is the correct Mathlib name and signature
  (`ℝ → ℝ`), hence the explicit coercions `Real.log (k : ℝ)`.
- Whether the binder chain `∀ (α : Type*) [DecidableEq α] (k r : ℕ), …` under an
  `∃ C` elaborates exactly as written. I believe instance-implicit binders are
  allowed in `∀`-telescopes; if not, the fix is to make `α`/`[DecidableEq α]`
  section `variable`s (mildly weakening the "`C` independent of `α`" reading) or
  to introduce `α` before `∃ C`.
- Mathlib may define its own `IsSunflower` / `Finset.IsSunflower` (I am not
  certain the sunflower lemma or its definition is currently in Mathlib). To
  avoid any clash the predicate is placed in `namespace Agent041`.
- No claim is made that a Mathlib lemma with this content exists; this is a
  from-scratch statement.
