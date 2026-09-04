# Agent 082 — formalization note

## What I stated

Three `sorry`-terminated theorems plus four auxiliary `def`s:

1. `boolean_degree_le_isJunta` — the **forward direction**: `∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, …`
   every Boolean degree-`≤ d` function on `binom([n],k)` is an `m`-junta.
2. `boolean_degree_le_not_isJunta` — the **converse**, stated literally as in the prompt:
   for `1 ≤ k < 2d`, `∀ m, ∃ n ≥ 2k`, a Boolean degree-`≤ d` non-`m`-junta on `binom([n],k)`.
3. `sliceProductFun_not_isJunta` — the **explicit witnessing family**
   `∏_{i<ℓ} (∑_{j<e} x_{i·e+j})` with `e = min d k`, asserting it is Boolean, degree `≤ d`,
   and not an `ℓ·e`-junta whenever `n ≥ 2·ℓ·e`.

## Encoding decisions

- **Ambient set / coordinates:** `Fin n`, matching `{1,…,n}`.
- **Slice:** carried informally — a function on the slice is `f : Finset (Fin n) → ℝ`, and
  every property is guarded by `S.card = k`. Chosen over `{S // S.card = k}` so the polynomial
  evaluation and the junta condition read directly without subtype plumbing.
- **Boolean codomain:** `ℝ` together with a predicate `IsBooleanOn` (`f S = 0 ∨ f S = 1`).
  Keeping `f` real-valued lets "agrees with a real polynomial" be stated as literal equality.
- **Degree `≤ d`:** `∃ p : MvPolynomial (Fin n) ℝ` with `p.totalDegree ≤ d`, multilinear
  (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), and `MvPolynomial.eval (IndicatorVec S) p = f S` for all
  `k`-sets `S`. `IndicatorVec S i = if i ∈ S then 1 else 0`. Multilinearity is included for
  fidelity to the prompt's "Terms"; it does not change the represented function class on the
  slice (since `x_i^2 = x_i` there), so it could be dropped.
- **Junta:** `∃ J, J.card ≤ m ∧ ∀ S T k-sets, S ∩ J = T ∩ J → f S = f T`. This is the standard
  "value depends only on `S ∩ J`" for the slice.
- **`m(d)`:** an existential *inside* the forward statement (`∃ m : ℕ, …`), with `m` quantified
  before `k` and `n`, so it depends only on `d`. Chosen over an explicit `m : ℕ → ℕ` because the
  prompt only claims existence and no closed form is specified.
- **Explicit family:** built from `blockSumPoly n e i = ∑ j<e, X ⟨i·e+j, _⟩` with an
  `if h : i·e+j < n then … else 0` guard so the polynomial is total (no inline `Fin n` bound
  proof needed). `sliceProductPoly = ∏ i<ℓ, blockSumPoly n (min d k) i`; the slice function is
  its evaluation at `IndicatorVec S`. Indexing is `0`-based (`i·e+j`, `i<ℓ`, `j<e`), the
  translation of the prompt's `1`-based `x_{(i-1)e+j}`.

## Uncertainties

- **Literal converse vs. the phenomenon.** With `d` and `k` both fixed, `∏_{i<ℓ} (∑_{j<e} x…)`
  restricted to `binom([n],k)` is identically `0` for `ℓ > k` and is `{0,1}`-valued and genuinely
  depends on `ℓ·e` coordinates essentially only at `ℓ = k` (the "transversal of `k` blocks"
  function), giving a non-junta of size `k·min(d,k)` — a *bounded* quantity for fixed `d`. So I
  believe the honest unbounded-junta statement needs `d` (or the pair `(d,k)`) to grow, and the
  prompt's "for every `m`" with `d` fixed over-reaches for this explicit family. I nonetheless
  transcribed the converse and the witness theorem literally (as requested: formalize the stated
  theorem), and flag that `sliceProductFun_not_isJunta` as written is likely provable only in the
  regime `ℓ ≈ k` (for `ℓ > d` the polynomial `sliceProductPoly` itself has `totalDegree = ℓ > d`,
  so `HasDegreeLEOn` would rely on a distinct lower-degree representative that may not exist).
- **Guessed Mathlib identifiers:** `MvPolynomial.totalDegree`, `MvPolynomial.eval` (used as a
  bundled hom applied to a point function and a polynomial), `MvPolynomial.support` (a
  `Finset (Fin n →₀ ℕ)`), and `Finsupp` application `t i` for `t ∈ p.support`. `MvPolynomial.X`
  for variables. All believed current, not compiler-checked.
- `import Mathlib` is used wholesale for safety; `∑ / ∏` notation assumed available without an
  explicit `open scoped BigOperators`.
