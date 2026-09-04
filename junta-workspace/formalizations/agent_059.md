# Agent 059 — formalization note

## What I stated

All three parts of the theorem, as separate `theorem ... := by sorry`:

1. `boolean_degree_d_junta_upper` — the junta **upper bound**: `∃ m : ℕ → ℕ`, then
   for all `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`, every Boolean degree-`≤ d` function on the
   slice is an `m d`-junta.
2. `boolean_degree_d_junta_lower` — the **converse in existence form**: for
   `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` carries a Boolean degree-`≤ d`
   non-`m`-junta.
3. `boolean_degree_d_junta_lower_witness` — the **converse with the explicit
   family** `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )`, `e = min d k`: for any
   `ℓ ≥ 1` and `n ≥ 2ℓe` the represented slice function is Boolean, degree `≤ d`,
   and not an `ℓe`-junta.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; membership/intersection are then plain `Finset` operations.
  Ambient size `n`, slice size `k`, degree `d` are all carried as explicit `ℕ`
  arguments; `n ≥ 2k` and `k ≥ 2d` (resp. `k < 2d`) as `2 * k ≤ n` etc.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain chosen so that "agrees
  with a real polynomial" is a direct equality with no coercion friction.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`, `p` multilinear,
  `p.totalDegree ≤ d`, and `∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S.1 then 1 else 0`. Multilinearity is spelled out by
  hand as `IsMultilinearPoly p : ∀ m ∈ p.support, ∀ i, m i ≤ 1` (squarefree
  support) since I do not believe Mathlib has a ready predicate for it. Requiring
  multilinearity matches the problem's wording; it does not change the represented
  function class or the minimal achievable degree (reducing `xᵢ^2 ↦ xᵢ` on `0/1`
  inputs never raises total degree), so this is equivalent to "min degree over all
  representatives".
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` (value depends only on `S ∩ J`).
- **m(d)**: existential *inside* the statement, as an explicit function
  `m : ℕ → ℕ` applied as `m d`, so the bound provably depends on `d` only.
- **Explicit family** (`witnessPoly n ℓ e`): `∏_{i ∈ range ℓ} Σ_{j ∈ range e} X_{i*e+j}`
  in `MvPolynomial (Fin n) ℝ`. Blocks are 0-indexed (`i*e+j`), equivalent to the
  problem's 1-indexed `x_{(i-1)e+j}`. The `Fin n` index is produced by a
  `dite (i*e+j < n)` that returns `0` on the (never-taken, given `n ≥ 2ℓe`)
  out-of-range branch — this keeps the definition total without threading the
  `n`-bound through the binders. `witnessPoly` is `noncomputable` only defensively.

## Uncertainties

- I trust the problem statement that the explicit product family is genuinely
  `{0,1}`-valued on the slice and collapses to degree `≤ d` there (the product of
  `ℓ` linear forms has *free* total degree `ℓ`; the degree-`≤ d` claim is via a
  different representative, which `HasDegreeLE` allows as an existential). I could
  not re-derive the Boolean-ness of the raw product from scratch; the statement is
  transcribed as given.
- Guessed / hand-rolled Mathlib identifiers: `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.X`, `(p : MvPolynomial _ _).support`
  with exponent access `m i` for `m : Fin n →₀ ℕ`. No Mathlib notion of "Boolean
  function on a slice" or "multilinear polynomial" is assumed to exist.
- `MvPolynomial.totalDegree 0 = 0`, so the zero polynomial legitimately witnesses
  degree `0` for the constant-`0` function; `C 1` similarly for constant `1`.
- `hℓ : 1 ≤ ℓ` is added in part 3 (with `ℓ = 0` the product is the constant `1`,
  which *is* a `0`-junta).
