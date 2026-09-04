# Agent 062 — note on the formalization

## What is stated

Two theorems, both `:= by sorry` (statement only):

1. `filmus_ihringer` — **both directions**:
   - *Junta direction*: `∃ m`, depending only on `d`, such that for all `k ≥ 2d`,
     all `n ≥ 2k`, every Boolean degree-`d` function on the slice is an `m`-junta.
   - *Sharpness direction*: for `1 ≤ k < 2d`, for every `m` there is `n ≥ 2k` and a
     Boolean degree-`d` function that is not an `m`-junta — stated **existentially**
     (no explicit witness).

2. `filmus_ihringer_witness` — the **explicit witnessing family** for the sharpness
   direction: `witnessPoly ℓ e = ∏_{i<ℓ} ∑_{j<e} X (i*e+j)`, with `e = min d k`,
   evaluated at the indicator vector (`witnessFun`). For every `m` one takes `ℓ` with
   `ℓ*e > m` and `n ≥ 2ℓe`; the function is asserted Boolean, degree `≤ d`, dependent on
   all `ℓ*e` block coordinates, and not an `m`-junta.

## Encoding decisions

- **Ambient coordinates: `ℕ`.** Variables of `MvPolynomial ℕ ℝ` are indexed by `ℕ`; the
  slice `binom([n],k)` is `{S : Finset ℕ // S.card = k ∧ ∀ x ∈ S, x < n}` (subsets of
  `{0,…,n-1}`). Chosen so the explicit family `∏_i ∑_j X (i*e+j)` needs no dependent
  `Fin n` index bounds — the arithmetic `i*e+j` is just on `ℕ`.
- **Boolean codomain: `ℝ` + predicate** `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Forced
  by the degree definition (agreement with a real polynomial); keeping one codomain
  avoids coercions.
- **Degree: `MvPolynomial (Fin →) ℝ` + `totalDegree`.** `HasDegreeLE d f` = there exists
  a polynomial `p` that is multilinear (`IsMultilinear p := ∀ t ∈ p.support, ∀ x, t x ≤ 1`,
  hand-rolled — no Mathlib predicate for this that I know of) with `p.totalDegree ≤ d`
  agreeing with `f` at every slice indicator vector. Existential over `p`, so the
  low-degree *representative* need not be the naive polynomial.
- **Junta:** `IsJunta m f := ∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T, S∩J = T∩J → f S = f T`.
- **`m(d)`:** existential `∃ m : ℕ` inside the statement, quantified after `d` but before
  `k, n`, so it depends on `d` only.
- **`e = min d k`** carried as a hypothesis `he : e = min d k`.
- Indices are `0`-based, so block `i` is `{i*e, …, i*e+e-1}` (paper's `(i-1)e+j`,
  `j = 1..e`).

## Uncertainties

- Guessed/assumed Mathlib identifiers: `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `MvPolynomial.support`, `MvPolynomial.X`, `Finsupp` application `t x` for
  `t : ℕ →₀ ℕ`. These are standard; API churn is possible but unlikely for these.
- No Mathlib "multilinear polynomial" predicate is used; `IsMultilinear` is defined
  directly.
- **Faithfulness of the explicit family.** I transcribed `∏_{i=1}^{ℓ} ∑_{j=1}^{e}
  x_{(i-1)e+j}` verbatim from the task. I did not verify that its slice-restriction is
  genuinely `{0,1}`-valued and of slice-degree `≤ d` for all `ℓ` — that is the paper's
  claim, and this is a statement-only formalization.
- The task's phrase "not `ℓe`-juntas" is rendered as `¬ IsJunta (ℓ*e - 1) …` (the
  function visibly *is* an `ℓ*e`-junta since it reads exactly the `ℓ*e` block
  coordinates; the intended content is that it depends on all of them). The separate
  `¬ IsJunta m …` clause, with `m < ℓ*e`, is the "for every `m`" conclusion.
- `witnessPoly` / `witnessFun` are marked `noncomputable` (real coefficients).
