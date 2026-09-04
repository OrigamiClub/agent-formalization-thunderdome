# Agent 096 — Filmus–Ihringer slice-junta theorem (statement only)

## What is stated

Three theorems, all `:= by sorry`, no proofs:

1. `boolean_degree_d_is_junta` — the **positive direction**: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d,
   ∀ n ≥ 2k, ∀ f`, if `f` is Boolean and has degree `≤ d` on the slice then `f` is an
   `M`-junta.
2. `boolean_degree_d_not_junta` — the **converse / sharpness**, as a pure existential:
   `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`, `∀ m, ∃ n ≥ 2k, ∃ f`, `f` is Boolean, has degree
   `≤ d`, and is **not** an `m`-junta.
3. `boolean_degree_d_not_junta_explicit` — the converse with the **explicit witnessing
   family** `FIpoly` / `FIfun` named in the statement: for every `m` there are `ℓ, n`
   (with `n ≥ 2·ℓ·e` and `n ≥ 2k`, `e = min d k`) making `FIfun d k n ℓ` a Boolean,
   degree-`≤ d`, non-`m`-junta function.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. `Fin n` stands for
  `{1,…,n}`. `n`, `k`, `d`, `m` are plain `ℕ` arguments carried with explicit
  inequality hypotheses (`2 * d ≤ k`, `2 * k ≤ n`, `k < 2 * d`, …).
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain was chosen so the function
  interfaces directly with polynomial evaluation (the degree notion) without a
  cast layer.
- **Degree ≤ d** (`HasDegreeLE`): there exists `p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ s ∈ p.support, ∀ i, s i ≤ 1`) and has `p.totalDegree ≤ d`, such that
  for every slice element `f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S.1 then 1 else 0`. This is the "restriction of a
  multilinear real polynomial of total degree ≤ d, evaluated at the indicator vector"
  reading from the prompt. Multilinearity is a harmless normalization on `{0,1}`
  inputs; I included it to match the prompt's wording "multilinear".
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J
  → f S = f T` — the value depends only on `S ∩ J`.
- **m(d)**: existential *inside* the statement (`∃ M : ℕ, …`) after fixing `d`, rather
  than a supplied `m : ℕ → ℕ`. Either is faithful; the existential is weaker to state
  and matches "there is a constant".
- **Explicit family** (`FIpoly d k n ℓ`): `∏_{i∈range ℓ} ∑_{j∈range (min d k)} x_{i·e+j}`
  with `e = min d k`, `0`-based block indexing (blocks `{i·e,…,i·e+e-1}`). Each
  variable index is `dite`-guarded by `i·e+j < n`; the out-of-range branch is `0` and
  never fires once `n ≥ 2·ℓ·e`. `FIfun` is `FIpoly` evaluated at the indicator vector.

## Uncertainties

- **Mathlib identifiers guessed from memory**: `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.X`, `MvPolynomial.support`, the `∑ x ∈ s, _`
  / `∏ x ∈ s, _` big-operator binder notation, `Finset.range`, `Finset.card`,
  `Finset.inter`. `import Mathlib` is used so everything is in scope; exact names may
  need adjustment.
- **"not `ℓe`-juntas"**: taken literally, a function whose value is determined by the
  `ℓe` block coordinates *is* an `ℓe`-junta, so I read the prompt's phrase as "these
  functions genuinely need `ℓe` relevant coordinates", i.e. not `m`-juntas for
  `m < ℓe`. In theorem 3 this is captured by leaving `ℓ` existential (chosen with
  `ℓe > m`) and asserting `¬ IsJunta m (FIfun d k n ℓ)`.
- **Correctness of the transcribed family**: I did not independently verify that
  `FIfun d k n ℓ` is Boolean and of slice-degree `≤ d` for all relevant `ℓ` — under a
  naive "disjoint block sums" reading the product can collapse on the slice for large
  `ℓ`. Because theorem 3 quantifies `ℓ` existentially and asserts `HasDegreeLE d` of the
  *slice function* (some degree-`≤ d` polynomial represents it, not necessarily
  `FIpoly` itself, whose raw total degree is `ℓ`), the statement leaves room for the
  true construction; but a reader should cross-check the family against the
  Filmus–Ihringer paper.
- **Index origin**: prompt uses `1`-based `x_{(i-1)e+j}` (`i=1..ℓ`, `j=1..e`); I used
  `0`-based `x_{i·e+j}` (`i=0..ℓ-1`, `j=0..e-1`). Same set of `ℓe` coordinates, shifted.
