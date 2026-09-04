# agent_099 — formalization note

## What is stated

All three as `theorem … := by sorry` (no proofs):

1. `juntas_of_degree_le` — the **positive direction**: for `d ≥ 1`, `∃ m`, such
   that `k ≥ 2d` and `n ≥ 2k` imply every Boolean degree-`d` function on the
   slice is an `m`-junta.
2. `not_juntas_of_degree_le` — the **negative direction, abstract**: for
   `1 ≤ k < 2d`, for every `m` there is a slice and a Boolean degree-`d`
   function on it that is not an `m`-junta.
3. `witness_not_junta` — the **negative direction with the explicit family**
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min(d,k)`, asserting Booleanity,
   degree `≤ d`, and failure to be an `ℓe`-junta, for `n ≥ 2ℓe`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` (not `def`) so `.val`, `.card`, `∩` work directly.
- **Boolean codomain**: functions valued in `ℝ` plus a predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  to avoid any coercion friction with the polynomial-evaluation degree notion.
- **Degree ≤ d**: `HasDegreeLE f d` = `∃ p : MvPolynomial (Fin n) ℝ`,
  `p.totalDegree ≤ d` and `f S = MvPolynomial.eval (indicator S.1) p` for all
  slice points, where `indicator S i = if i ∈ S then 1 else 0`. This is the
  "agrees on the slice with a real polynomial of total degree ≤ d evaluated at
  the indicator vector" definition from the problem statement. Multilinearity is
  not imposed (equivalent on the slice).
- **m-junta**: `IsJunta f m` = `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **`m(d)`**: existential `∃ m : ℕ` after fixing `d` (i.e. "there is a constant
  depending on `d`"), rather than a global explicit `m : ℕ → ℕ`. Either is
  faithful; the existential keeps the statement lighter.
- **`n`, `k`, `d`**: plain `ℕ` arguments; ambient coordinate set is `Fin n`.
  Hypotheses transcribed literally: `2 * d ≤ k`, `2 * k ≤ n` (positive);
  `1 ≤ k`, `k < 2 * d` (negative).
- **Explicit family**: `witnessPoly n e ℓ` uses `i ∈ range ℓ`, `j ∈ range e`,
  reindexing the `1`-based `(i-1)e+j` to the `0`-based `i*e+j`, so variables
  `x_0 … x_{ℓe-1}` are used. Out-of-range indices (only when `ℓe > n`) are sent
  to `0` via `dite`, so the `def` carries no side proof obligation.
  `witnessFun` evaluates it at the indicator vector. `witness_not_junta` picks
  `ℓ` with `ℓ * min d k > m` and asserts the properties for all `n ≥ 2ℓe` and
  `n ≥ 2k`.

## Uncertainties

- **Mathlib identifiers** (used, believed current): `MvPolynomial`,
  `MvPolynomial.X`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `Finset.range`, big-operator `∏ … ∈ …` / `∑ … ∈ …`. `open scoped BigOperators`
  may be redundant/deprecated in recent Mathlib but should be harmless.
- **`witness_not_junta` is transcribed on faith.** I did not re-derive that the
  literal product `∏(∑ x)` (naive total degree `ℓ`) has slice-degree `≤ d`, nor
  that it is `{0,1}`-valued on `binom([n],k)` for the intended `ℓ`. My own quick
  analysis suggested the product is Boolean on `binom([n],k)` essentially when
  `ℓ = k` (it becomes the indicator that `S` is a transversal of the `ℓ` size-`e`
  blocks), which would depend on exactly `ℓe` coordinates and hence *be* an
  `ℓe`-junta. The problem says "not `ℓe`-juntas"; I kept that literal wording,
  but the mathematically sharp claim is likely "not an `(ℓe−1)`-junta"
  (equivalently: minimal junta arity is exactly `ℓe`, hence unbounded). The
  combination `m < ℓ * min d k` together with `¬ IsJunta … (ℓ * min d k)` still
  yields `¬ IsJunta … m`, which is the intended consequence. If the intended
  reading is different (e.g. `k` is also chosen, or a different normalization of
  the factors such as `∑ x_j − 1`), `witness_not_junta` would need adjustment;
  `not_juntas_of_degree_le` is the safe abstract version and does not depend on
  these details.
- The positive direction's hypothesis is taken exactly as given (`k ≥ 2d`,
  `n ≥ 2k`); the underlying paper may phrase it via `min(k, n−k)`.
