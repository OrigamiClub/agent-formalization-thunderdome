# agent_001 — formalization note

## What is stated

Three `:= by sorry` theorems (statements only, nothing proved):

1. **`slice_boolean_degree_junta`** — the positive direction: for `d ≥ 1` there is
   `M : ℕ` (bound after `d` is fixed, so it depends only on `d`) such that for all
   `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
   `M`-junta.
2. **`slice_boolean_degree_not_junta`** — the converse in clean existential form:
   for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` carries a Boolean degree-`d`
   function on `binom([n],k)` that is not an `m`-junta.
3. **`witness_properties`** — the explicit witnessing family: for `1 ≤ k < 2d`, any
   `ℓ`, and `n ≥ 2·ℓ·e` (`e = min d k`), the function
   `witness n k d ℓ : S ↦ ∏_{i<ℓ} |S ∩ Bᵢ|` is Boolean on the slice, has degree
   `≤ d`, and is not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; direct, and set intersection `S ∩ J` (used for juntas) is
  available. Ambient coordinate set is `Fin n`; `n`, `k`, `d`, `ℓ` are plain `ℕ`
  arguments/binders.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f := ∀ x, f x = 0 ∨ f x = 1`. Chosen over `Bool` / `Fin 2` / `ZMod 2`
  so that "agrees with a real polynomial" needs no coercion gymnastics.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, multilinear (`∀ i, MvPolynomial.degreeOf i p ≤ 1`), and
  `f x = MvPolynomial.eval (ind x.1) p` on every slice point, where
  `ind S i = if i ∈ S then 1 else 0`. This is the "restriction of a real
  multilinear polynomial evaluated at the indicator vector" definition. The
  multilinearity clause is mathematically inessential (multilinearizing on
  `{0,1}`-inputs preserves values and does not raise total degree) but is kept to
  match the theorem's wording.
- **`m`-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `x.1 ∩ J = y.1 ∩ J → f x = f y`. `J` lives in `Fin n`; the bound `m` is a
  separate `ℕ` not tied to `n`, which is the whole point of the positive direction.
- **`m(d)`**: an existential `∃ M : ℕ` placed after `d` is fixed — no explicit
  `m : ℕ → ℕ`. Simpler, and the theorem only claims existence of the constant.
- **Explicit family**: `block n e i := univ.filter (fun c => i*e ≤ c.val ∧ c.val < (i+1)*e)`
  is the `i`-th block of `e = min d k` consecutive coordinates; `witness n k d ℓ x
  = ∏ i ∈ range ℓ, (x.1 ∩ block n (min d k) i).card`. Each factor
  `(x ∩ Bᵢ).card` is exactly `∑_{j=1}^{e} x_{(i-1)e+j}` on the slice, so the
  product matches `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`. Degree `≤ d` is asserted
  via `HasDegreeLE` (existential over polynomials) rather than exhibiting the
  degree-reducing polynomial, since that reduction is the hard content.

## Interpretation / faithfulness choices

- The task's phrase "for `n ≥ 2ℓe` are not `ℓe`-juntas" is taken to mean the
  witnesses genuinely need all `ℓ·e` coordinates: `witness` depends only on
  coordinates `< ℓ·e`, so it *is* literally an `ℓ·e`-junta; the non-trivial claim
  is that it is **not** an `m`-junta for any `m < ℓ·e`. That is what is stated. The
  side condition `n ≥ 2·ℓ·e` is carried over verbatim from the task.
- I did not independently verify that `witness` is `{0,1}`-valued for all
  `1 ≤ k < 2d`; the naive pointwise product `∏ |S ∩ Bᵢ|` need not be. The theorem
  asserts Booleanness because the source theorem does; the `sorry` stands in for
  the paper's argument.

## Uncertainties (guessed Mathlib identifiers)

- `MvPolynomial.degreeOf` — assumed signature `degreeOf (i : σ) (p) : ℕ`
  (variable first). If the argument order is reversed, the multilinearity clause
  needs `MvPolynomial.degreeOf p i`.
- `MvPolynomial.totalDegree`, `MvPolynomial.eval` — assumed present with the usual
  signatures (`eval : (σ → R) → MvPolynomial σ R → R` as a ring hom applied to `p`).
- `Finset.filter` used with an inferred `DecidablePred` for the arithmetic
  predicate defining `block`; should resolve without `Classical`.
- `import Mathlib` (whole library) for self-containedness.
