# Agent 027 — formalization note

## What is stated

Both directions, in one theorem `boolean_constant_degree_slice_junta`, for a fixed
`d` with hypothesis `hd : 1 ≤ d`, as a conjunction:

1. **Forward** (`k ≥ 2d`): `∃ m : ℕ`, for all `k, n` with `2d ≤ k` and `2k ≤ n`,
   every Boolean degree-`d` function on the slice is an `m`-junta. The constant
   `m(d)` is an existential *inside* the statement (quantified after `d` is fixed),
   matching "there is a constant `m(d)`".

2. **Converse** (`1 ≤ k < 2d`): for every `k` in that range and every `m`, there
   exist `n`, `ℓ` with `n ≥ 2k`, `n ≥ 2·ℓ·(min d k)`, and `m < ℓ·(min d k)`, such
   that the explicit function `wedgeFun n k ℓ (min d k)` is Boolean, has slice
   degree `≤ d`, and is **not** an `m`-junta.

The explicit witnessing family is included: `wedgePoly` is
`∏_{i=0}^{ℓ-1}(∑_{j=0}^{e-1} X_{i·e+j})` and `wedgeFun` is its evaluation at
indicator vectors.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; the ambient coordinate set is `Fin n`, and `n, k, d` are plain
  `ℕ` arguments.
- **Boolean codomain**: real-valued functions `Slice n k → ℝ` with a separate
  predicate `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen so that "degree" can be
  phrased directly via real polynomials without a coercion.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity, as in the informal
  statement), `p.totalDegree ≤ d`, and `∀ S, f S = MvPolynomial.eval (indicator S.1) p`.
  Agreement is required only on the slice. `indicator S i = if i ∈ S then 1 else 0`.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` ("value depends only on `S ∩ J`").
- **Explicit family**: `wedgePoly n ℓ e hn` uses `Finset.range` products/sums; the
  coordinate `i·e + j` is coerced into `Fin n` as `⟨(i*e+j) % n, _⟩`. The `% n` is
  cosmetic — under the stated bound `n ≥ 2·ℓ·e` all indices `< n` already — and
  keeps the definition total without extra index-arithmetic hypotheses. `hn : 0 < n`
  is carried explicitly so the `Fin.mk` proof goes through.

## Interpretation choices / uncertainties

- The task's phrase "…which for `n ≥ 2ℓe` are not `ℓe`-juntas" is, read literally,
  not what one wants: `wedgeFun` manifestly depends on exactly the `ℓe` coordinates
  `{0,…,ℓe−1}`, so it *is* an `ℓe`-junta. I took the intended meaning to be the
  mechanism behind "for every `m` … not an `m`-junta": given `m`, choose `ℓ` with
  `ℓ·e > m`, making the function depend on `> m` relevant coordinates. Hence the
  converse concludes `¬ IsJunta m (wedgeFun …)` together with `m < ℓ * min d k`.
- Multilinearity is encoded as `degreeOf i p ≤ 1` for all `i`. There is no
  dedicated `MvPolynomial` "is multilinear" predicate in Mathlib that I am
  confident of; this is the standard surrogate. On `0/1` inputs it is anyway WLOG,
  so one could also drop the `degreeOf` clause.
- `wedgePoly`'s own `totalDegree` is `ℓ`, not `≤ d`; `HasSliceDegreeLE` is
  satisfied by a *different* polynomial agreeing with it on the slice (the crux of
  the Filmus–Ihringer construction). This is intended and is why the definition is
  an existential over `p`.
- Guessed / relied-on Mathlib identifiers: `MvPolynomial.degreeOf`,
  `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X`,
  `Nat.mod_lt`, `Finset.range`, big-operator notation `∏ i ∈ s, …` / `∑ j ∈ s, …`.
  Argument order of `MvPolynomial.degreeOf` (coordinate first, polynomial second)
  is assumed. `import Mathlib` is used to avoid import-path guessing.
- `m(d)` is an existential inside the statement rather than an explicit
  `m : ℕ → ℕ`; the explicit-family lower bound needs only the qualitative
  "no uniform bound" form.
