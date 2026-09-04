# Agent 010 — formalization note

## What I stated

All three pieces, as separate `theorem`s (all `:= by sorry`):

1. `boolean_degree_junta` — forward direction: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k`, every
   Boolean degree-`≤ d` function on the slice is an `M`-junta. `m(d)` is an existential
   `∃ M : ℕ` placed at the front, so `M` depends only on `d`.
2. `boolean_degree_not_junta` — converse in pure existential form: `∀ d ≥ 1`, `∀ 1 ≤ k < 2d`,
   `∀ m`, there exist `n ≥ 2k` and a Boolean degree-`≤ d` function on the slice that is not
   an `m`-junta.
3. `witnessFn` + `witnessFn_spec` — the explicit family: a concrete `def` and the claim that
   it is Boolean, degree `≤ d`, and not an `m`-junta for any `m < ℓ·e` (with `e = min d k`).

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`;
  simplest carrier for both "indicator vector" and "S ∩ J".
- **Boolean codomain**: functions are `Slice n k → ℝ` with a separate `IsBoolean` predicate
  (`∀ S, f S = 0 ∨ f S = 1`). Chosen over `Bool`/`Fin 2`/`ZMod 2` because the degree notion
  is about real polynomials; keeping `f` real-valued removes all coercion friction between
  `f S` and `eval … p`.
- **Degree ≤ d**: `HasDegreeLE f d` = `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`
  and `f S = eval (indicator S.1) p` for every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. Permissive (not restricted to multilinear `p`)
  because `x_i^2 ↦ x_i` on `{0,1}` inputs keeps the total degree, so the two forms cut out
  the same function class; I noted this in the file.
- **m-junta**: `IsJunta f m` = `∃ J : Finset (Fin n)`, `J.card ≤ m`, and for all slice
  points `S T`, `S.1 ∩ J = T.1 ∩ J → f S = f T`. Standard "depends only on `S ∩ J`".
- **n, k, d, coordinates**: all explicit `ℕ` arguments; ambient coordinate set is `Fin n`.
  Inequalities as `2 * d ≤ k`, `2 * k ≤ n`, `k < 2 * d`.
- **Explicit family indexing**: blocks indexed by `Fin ℓ`, within-block by `Fin e` with
  `e = min d k` passed as a parameter plus `he : e = min d k`. `blockCoord` embeds
  `(i, j)` into `Fin n` via `finProdFinEquiv : Fin ℓ × Fin e ≃ Fin (ℓ*e)` then
  `Fin.castLE`. The room hypothesis is `hn : 2 * (ℓ * e) ≤ n`.

## Uncertainties / guessed identifiers

- `finProdFinEquiv` (Mathlib, `Mathlib/Logic/Equiv/Fin.lean`) — believed to be
  `Fin m × Fin n ≃ Fin (m * n)`. Only its injectivity is needed; exact mapping formula and
  argument order are not load-bearing, but the name/shape is a guess.
- `Fin.castLE (h : n ≤ m) : Fin n → Fin m` — name/signature from memory.
- The three `(by omega)` obligations in `witnessFn_spec` discharge `ℓ * e ≤ n` from
  `2 * (ℓ * e) ≤ n`; this relies on `omega` treating `ℓ * e` as an opaque atom. If that
  fails, replace with an explicit `Nat.le_trans` term.
- **Source formula discrepancy**: the theorem text gives the witnesses as a product of sums
  `Π_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`. That polynomial is not `{0,1}`-valued on the
  slice (a size-`k` set can meet a block in ≥ 2 points, or miss all blocks giving a
  constant). I formalized instead the sum of degree-`e` monomials
  `Σ_{i} Π_{j} x_{(i-1)e+j}` = "some block sits inside `S`", which *is* Boolean (since
  `k < 2d ⟹ k < 2e`), has slice-degree `≤ e ≤ d`, and depends on all `ℓe` block
  coordinates. I read this as the intended object and flagged it in the file.
- **"not `ℓe`-juntas"**: taken to mean "not an `m`-junta for any `m < ℓe`", i.e. `ℓe` is the
  count of relevant coordinates. The function itself *is* an `ℓe`-junta, so a literal
  `¬ IsJunta f (ℓ*e)` would be false; hence the `∀ m < ℓ*e` form.
- Only the *statements* are given; truth of `witnessFn_spec` was checked informally
  (Booleanity via `k < 2e`, degree via `e ≤ d`, non-junta via a spare coordinate that
  exists when `n ≥ 2ℓe`), not proved.
