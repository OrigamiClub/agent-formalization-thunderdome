# agent_022 — improved sunflower lemma (statement only)

## Form chosen

A single existential theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    HasSunflower W r
```

with two auxiliary definitions, `IsSunflower` and `HasSunflower`.

## Encoding decisions

- **Set family representation:** `Finset (Finset α)` over an arbitrary ambient
  type `α` with `[DecidableEq α]`. This is the standard Mathlib idiom for finite
  set-family combinatorics (e.g. the Kruskal–Katona development) and makes
  "finite family" and "each set finite of size `k`" automatic. `Set`-based
  encodings would need extra finiteness hypotheses.
- **Cardinality:** `Finset.card` throughout (`S.card = k`, `𝒮.card = r`,
  `W.card`).
- **Distinctness** of the `r` sunflower sets: automatic — a sunflower is a
  `𝒮 : Finset (Finset α)` with `𝒮.card = r`, so its members are distinct by
  construction. No separate clause.
- **Sunflower predicate:** defined locally as "pairwise intersections all
  coincide": `∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y`. For `|𝒮| ≥ 2` this is
  equivalent to the explicit-core / disjoint-petals formulation and already
  forces `Y ⊆ S` and `Y = S ∩ T`, so I did not add those clauses. The core `Y`
  is existentially bound in `HasSunflower`.
- **Petals nonempty:** not required (matches the usual statement; at most one
  member can equal the core).
- **Constant `C`:** existentially quantified *inside* the theorem, and placed
  before the quantifier over `α`, so it is a true absolute constant independent
  of the ambient type. Sign constraint `0 < C` included.
- **Logarithm:** `Real.log` (natural log). Base is irrelevant because it is
  absorbed into `C`. The inequality lives in `ℝ`; `k`, `r`, `W.card` are coerced
  from `ℕ`. `^ k` is the natural-number power.
- **Degenerate `k`:** handled by the hypothesis `2 ≤ k`. With `Real.log`, any
  pure logarithm gives `log 1 = 0`, which would make the bound `0` and the
  statement false at `k = 1` (need `|W| ≥ r`, not just `|W| ≥ 1`). `k = 1` is
  trivial anyway. `k = 0` similarly excluded. Chose this over the alternative
  `Real.log k + 1` / `Real.log (k+1)` conventions to keep the bound in the
  recognizable `(C r log k)^k` shape.
- **`r`:** hypothesis `1 ≤ r` ("positive integers `r`"). `r = 0` is vacuous
  (empty subfamily) and dropped.

## Uncertainties

- No dependence on any Mathlib sunflower API: I believe Mathlib has **no**
  sunflower lemma / `Sunflower` predicate, so `IsSunflower` / `HasSunflower` are
  defined from scratch. If one exists (plausible names: `Finset.IsSunflower`,
  `SetFamily.Sunflower`), it should be preferred.
- Identifiers used: `Real.log`, `Finset.card`, `Finset.instInter` (`S ∩ T`),
  `Finset` subset `⊆`, all standard and high-confidence.
- The precise refined bound in the literature is sometimes written
  `(C r log k)^k` (Bell–Chueluecha–Warnke) and sometimes `(C r log(rk))^k`
  (Rao); I formalized exactly the `(C r log k)^k` form given in the task.
- Placing `∃ C, 0 < C ∧ ∀ {α} [DecidableEq α], …` (binders after the
  existential, with an instance binder) is valid Lean 4 term syntax as far as I
  know, but not machine-checked here.
