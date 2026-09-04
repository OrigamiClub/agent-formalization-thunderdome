# Agent 039 — formalization note

## What I stated

Both directions, plus the explicit witnessing family in the converse.

- `boolean_degree_junta_forward` — the junta direction. `∃ M : ℕ → ℕ` such that for all
  `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`, every Boolean degree-`d` function on the slice is an
  `M d`-junta.
- `boolean_degree_junta_converse` — the non-junta direction for `1 ≤ k < 2d`, including
  the block product-of-sums family `∏_{i<ℓ} ∑_{j<e} x_{i·e+j}` with `e = min d k`, and
  the claim that it fails to be an `ℓe`-junta (and hence an `m`-junta) once `ℓe > m` and
  `n ≥ 2ℓe`.

Both are `:= by sorry`. No proofs, including no auxiliary lemmas.

## Encoding decisions

- **Ground set**: `Fin n` (stands in for `{1,…,n}`). `n, k, d` are carried as explicit
  `ℕ` binders.
- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`,
  which makes `S ∩ J`, indicator vectors, and membership all directly available.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real values are needed anyway to talk about
  agreement with a real polynomial, so this avoids a `Bool`/`ℝ` coercion.
- **Degree ≤ d** (`HasDegreeLE`): there is `p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ i, p.degreeOf i ≤ 1`) and has `p.totalDegree ≤ d`, with
  `f S = MvPolynomial.eval (indicator S.1) p` for every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. This mirrors the "Terms" wording ("agrees on
  the slice with a multilinear real polynomial of total degree ≤ d evaluated at the
  indicator vector") literally.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J →
  f S = f T`. "Value depends only on `S ∩ J`" is rendered as the congruence property,
  which is the standard extensional reading and needs no quotient.
- **`m(d)`**: an existential `∃ M : ℕ → ℕ` inside the forward statement ("there is a
  constant `m(d)`"), universally quantified over `d ≥ 1`.
- **Explicit family**: rather than build a polynomial with dependent index proofs, the
  coordinate indexing is an existentially quantified `c : Fin ℓ → Fin e → Fin n` pinned
  down by `(c i j : ℕ) = i * e + j` (`e = min d k`, written `min d k` throughout). Such a
  `c` exists precisely because `n ≥ 2ℓe` forces `i*e+j < ℓe ≤ n`. The function is then
  `f S = ∏ i, ∑ j, (if c i j ∈ S then 1 else 0)`, i.e. the block sum-of-indicators
  product. `ℓ` is existentially chosen with `ℓ * e > m`; `n ≥ 2k` and `n ≥ 2ℓe` are both
  taken as hypotheses so the "there exist `n ≥ 2k`" clause is respected.
- The converse asserts both `¬ IsJunta f (ℓ*e)` (the sharp "not an `ℓe`-junta" claim)
  and the redundant-but-literal `¬ IsJunta f m`.

## Uncertainties

- `MvPolynomial.degreeOf` — used for the multilinearity clause. I am fairly confident of
  the name and signature (`degreeOf : σ → MvPolynomial σ R → ℕ`), but did not verify
  against a compiler. `MvPolynomial.totalDegree` and `MvPolynomial.eval` I am confident
  about.
- Including multilinearity at all is a choice: the "Terms" text says "multilinear", so I
  encoded it; the essential content is `totalDegree ≤ d`. Dropping the `degreeOf` clause
  would give a slightly weaker forward hypothesis / stronger converse claim, both still
  faithful.
- The family's Boolean-ness and its degree-`d`-ness are stated as *part of* the converse
  conjunction, not verified. Note the naive product `∏_{i<ℓ} ∑_{j<e} x` has total degree
  `ℓ`, not `d`; `HasDegreeLE f d` for it relies on slice identities (e.g. `∑ all x_i = k`
  is constant on the slice). That reduction is genuine mathematical content of the
  theorem and is left inside the `sorry`.
- Big-operator notation (`∏ i : Fin ℓ, …`) is assumed available from `import Mathlib`
  after `open Finset`, without a separate `open scoped BigOperators`.
- `min d k` is used as the literal value of `e`; with `d ≥ 1` and `k ≥ 1` it is `≥ 1`, so
  `Fin (min d k)` is nonempty, though the statement does not depend on that.
