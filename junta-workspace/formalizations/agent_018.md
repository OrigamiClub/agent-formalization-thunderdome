# Agent 018 — formalization note

## What I stated

All three pieces, as separate `theorem ... := by sorry` (plus supporting `def`s):

1. `filmus_ihringer_junta_bound` — positive direction: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`d` function on the slice is an `m`-junta.
2. `filmus_ihringer_no_junta_bound` — converse: for `1 ≤ k < 2d`, for every `m` there is
   `n ≥ 2k` and a Boolean degree-`d` function that is not an `m`-junta (pure existential witness).
3. `filmus_ihringer_explicit_family` — the same converse, but with the concrete family
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, asserting Boolean-ness,
   degree ≤ `d`, non-`ℓe`-junta and non-`m`-junta for `n ≥ 2ℓe`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`
  keeps `S ∩ J` (needed for the junta definition) literally a `Finset` intersection.
  `abbrev` (not `def`) so `.val` / `.property` and defeq unfold work without friction.
- **Boolean codomain**: functions valued in `ℝ`, with an explicit
  `∀ S, f S = 0 ∨ f S = 1` clause inside `BooleanDegreeLE`. Chosen over `Bool`/`Fin 2`
  so that "agrees with a real polynomial" is a plain equation in `ℝ` with no coercion layer.
- **Degree ≤ d**: `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`, `p` multilinear,
  and `∀ S, f S = eval (indicator S.val) p` where `indicator S i = if i ∈ S then 1 else 0`.
  The polynomial is existential, so only its behaviour on the slice matters — this is the
  intended "degree on the slice" (a function can have naive-degree > d yet a degree-≤d
  representative on the slice). Multilinearity is a hand-rolled predicate
  `∀ c ∈ p.support, ∀ i, c i ≤ 1`.
- **m-junta**: `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.val ∩ J = T.val ∩ J → f S = f T`.
- **m(d)**: existential `∃ m : ℕ` inside the statement, positioned after `d` and before
  `k, n, f`, so it depends on `d` only. Not exposed as an explicit `m : ℕ → ℕ`.
- **Explicit family**: `familyPoly n e ℓ` uses `∏` over `range ℓ` of `∑` over `range e`,
  with a `dite` guard `if h : i*e+j < n then X ⟨i*e+j,h⟩ else 0` to stay total without a
  side proof; for `n ≥ ℓe` the guard is always true so it is the intended polynomial.
  `familyFun` is its evaluation at indicator vectors. Indexing is 0-based
  (`(i-1)e+j` with `i,j ≥ 1` becomes `i*e+j` with `i,j ≥ 0`).
- **Carrying `n, k, d`**: all explicit `∀`-bound `ℕ`s; ambient coordinate set is `Fin n`.
  Inequalities as `2 * d ≤ k`, `2 * k ≤ n`, `k < 2 * d`, `1 ≤ k`, `1 ≤ d`.

## Uncertainties

- Mathlib identifiers assumed: `MvPolynomial`, `MvPolynomial.eval`, `MvPolynomial.X`,
  `MvPolynomial.totalDegree`, `MvPolynomial.support`, `Finset.range`, `Finset.prod`/`∏`,
  `Finset` `∩`. Names/signatures are from memory; `eval` is used applied as a function
  (it is a bundled ring hom).
- `Multilinear` is my own predicate; Mathlib may have a preferred spelling
  (e.g. via `MvPolynomial.degreeOf` or squarefree monomials) that I did not use.
- I did not encode a separate "restriction from the hypercube" or Johnson-scheme /
  Fourier-level notion of degree; only the polynomial-representation one.
- For `filmus_ihringer_explicit_family` I assert, verbatim from the theorem text, that
  `familyFun` is `{0,1}`-valued and of degree ≤ `d` on the slice and is *not* an
  `ℓe`-junta. The mechanism by which a product-of-block-sums polynomial (naive degree `ℓ`)
  becomes Boolean and degree-`d` on the slice, and how it fails to be an `ℓe`-junta despite
  syntactically involving only the first `ℓe` variables, is taken on faith from the problem
  statement — I could not fully reconstruct it from memory. The abstract converse
  (`filmus_ihringer_no_junta_bound`) does not depend on these details.
- Whether `open scoped BigOperators` is still required for `∏` notation in the current
  Mathlib: I relied on it being globally available after `import Mathlib`.
