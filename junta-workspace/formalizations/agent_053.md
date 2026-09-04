# agent_053 — Filmus–Ihringer slice junta theorem (statement only)

## What is stated

All three parts, as separate `theorem … := by sorry`:

1. `slice_degree_junta` — the forward direction, with `m(d)` as an existential
   `∃ M : ℕ → ℕ` at the head of the statement.
2. `slice_degree_not_junta` — the converse (`1 ≤ k < 2d` ⇒ no uniform junta bound).
3. `witness_not_junta` — the explicit witnessing family
   `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, asserting it is Boolean on
   the slice, degree `≤ d`, and not an `(ℓ·e)`-junta once `n ≥ 2·ℓ·e` (and `n ≥ 2k`).

Nothing is proved.

## Encoding decisions

- **Slice.** Not reified. A function "on the slice `binom([n],k)`" is a total function
  `f : Finset (Fin n) → ℝ`, and every predicate/claim quantifies over
  `S : Finset (Fin n)` guarded by `S.card = k`. This keeps `MvPolynomial` evaluation and
  the junta definition completely first-order and avoids subtype/`Sym` plumbing. The
  ambient coordinate set is `Fin n`; `n, k, d` are plain `ℕ` arguments.
- **Boolean codomain.** Real-valued (`ℝ`), with "Boolean" meaning `f S = 0 ∨ f S = 1` for
  slice `S` (`IsBooleanOnSlice`). Chosen because degree is defined via real polynomials, so
  a single codomain avoids casts.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity, matching "a
  multilinear real polynomial"), and `f S = MvPolynomial.eval (indicatorVec n S) p` for all
  slice `S`. The indicator vector is `fun i => if i ∈ S then (1:ℝ) else 0`.
  Note: on the 0/1 slice, "agrees with a multilinear poly of total degree ≤ d" and "agrees
  with any poly of total degree ≤ d" are equivalent (reduce `x_i^2 ↦ x_i`), so the
  multilinearity clause does not change the mathematical content; it is included for
  fidelity to the wording.
- **m-junta** (`IsSliceJunta`): `∃ J : Finset (Fin n), J.card ≤ m` and for all slice `S, T`,
  `S ∩ J = T ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`" formulation.
- **m(d)**: existential `∃ M : ℕ → ℕ` inside `slice_degree_junta` (the theorem asserts a
  bounding function exists), rather than an externally supplied explicit `M`.
- **Explicit family indexing.** `witnessPoly n ℓ e h` with `h : ℓ * e ≤ n` is
  `∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (Fin.castLE h (finProdFinEquiv (i, j)))`.
  The `ℓ·e` variables land injectively on the first `ℓ·e` coordinates of `Fin n`; the
  block partition into `ℓ` blocks of size `e` is the pushforward of the product structure
  under `finProdFinEquiv`, so the exact numbering of variables within `(i-1)e + j` may
  differ from the paper's by a fixed bijection (immaterial for "is / is not a junta").
  `witnessFun` evaluates this at indicator vectors. The family is indexed by `ℓ`; given `m`
  in the converse one takes `ℓ` with `ℓ·e > m` and `n ≥ max (2k) (2ℓe)`.

## Uncertainties / guessed identifiers

- `finProdFinEquiv : Fin ℓ × Fin e ≃ Fin (ℓ * e)` — name and the `ℓ * e` (vs `e * ℓ`)
  orientation are from memory; if wrong, replace with any explicit
  `Fin ℓ × Fin e ≃ Fin (ℓ * e)` or an inline `⟨i * e + j, _⟩`.
- `Fin.castLE : (h : a ≤ b) → Fin a → Fin b` — believed correct (used applicatively).
- `MvPolynomial.degreeOf : σ → MvPolynomial σ R → ℕ`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval : (σ → R) → MvPolynomial σ R → R`, `MvPolynomial.X` — standard, argument
  orders believed correct (`degreeOf i p`, `eval f p`).
- `witness_not_junta` carries both `hle : ℓ * min d k ≤ n` (needed as a term to build the
  polynomial) and `hn : 2 * (ℓ * min d k) ≤ n`; the former is redundant given the latter but
  is passed explicitly to avoid an inline proof term in the statement.
- Non-emptiness of the slice / `k ≤ n` is implied by the stated `2 * k ≤ n` hypotheses.
