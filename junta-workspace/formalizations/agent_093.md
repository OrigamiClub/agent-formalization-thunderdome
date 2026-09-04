# Agent 093 — formalization note

## What is stated

Statement only, three theorems, each `:= by sorry`:

1. `FilmusIhringer.forward` — positive direction: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`d` function on `binom([n],k)` is an `M`-junta. `M` is an
   existential *inside* the statement, bound before `k`/`n`, so it depends only on `d`
   ("there is a constant `m(d)`").
2. `FilmusIhringer.converse` — converse: `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`, `∀ m`,
   `∃ n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.
   Stated as a pure existential (no explicit witness).
3. `FilmusIhringer.explicit_family` — the explicit witnessing family, as a separate
   theorem (see below).

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Standard Mathlib
  idiom; `abbrev` so `.1`/`S.1 ∩ J` elaborate without unfolding friction. Ambient
  coordinate set is `Fin n`, with `n` carried as an explicit argument.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued (not `Bool`/`Fin 2`) so that the
  degree condition can be phrased directly via polynomial evaluation.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (every exponent `t i ≤ 1` for `t ∈ p.support`),
  and `f S = MvPolynomial.eval (charVec S.1) p` for every slice point, where
  `charVec S i = if i ∈ S then 1 else 0`. Multilinearity is included to match the
  "multilinear real polynomial" wording; it is w.l.o.g. on the `0/1`-cube.
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` (value depends only on `S ∩ J`).
- **m(d)**: existential `∃ M : ℕ` inside the statement rather than an explicit
  `m : ℕ → ℕ`; the theorem only asserts existence of a constant.

## Explicit family (`explicit_family`)

For `1 ≤ k < 2d`, put `e = min d k`. For every `ℓ` the theorem provides `n` (with
`n ≥ 2k` and `n ≥ 2ℓe`), a block family `B : Fin ℓ → Finset (Fin n)` with
`(B i).card = e` and pairwise disjoint, and `f` with
`f S = if ∃ i, B i ⊆ S.1 then 1 else 0`; it asserts `IsBoolean f`, `HasDegreeLE f d`,
and `¬ IsJunta f m` for every `m < ℓe`.

Interpretation choices / deviations from the literal prompt:

- The prompt writes the witness as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`. Taken
  literally as a polynomial this has total degree `ℓ` and is *not* Boolean on the slice
  (e.g. `d=2, k=3, e=2`, blocks `{1,2},{3,4}`, `S={1,2,3}` gives value `2`). I therefore
  read that expression as shorthand for the actual Filmus–Ihringer construction: the OR
  over `ℓ` disjoint `e`-blocks of the AND of a block,
  `f = ⋁_{i=1}^{ℓ} ⋀_{j=1}^{e} x_{(i-1)e+j}`. The hypothesis `k < 2d` is exactly
  `k < 2e`, which forbids a `k`-set from containing two disjoint blocks, so on the slice
  this `f` agrees with the degree-`e` (`≤ d`) polynomial `Σ_i ∏_{j∈B i} x_j` and is
  `{0,1}`-valued.
- The blocks are stated abstractly (a disjoint family of `e`-sets) rather than pinned to
  the literal index set `{(i-1)e+1,…,ie}`, to avoid `Fin n` bound arithmetic in a
  statement-only file. The concrete consecutive blocks are the intended instance and are
  described in the docstring/note.
- "not `ℓe`-juntas" is rendered as `∀ m < ℓe, ¬ IsJunta f m` (equivalently: all `ℓe`
  coordinates are relevant, so `f` is not an `(ℓe−1)`-junta). The literal reading
  "not an `ℓe`-junta" is false for a function on `ℓe` coordinates under the usual
  `≤ m` convention, so I took the mathematically intended meaning.

## Uncertainties

- Mathlib identifiers assumed: `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `MvPolynomial.support`, `Finsupp` application `t i` for `t : Fin n →₀ ℕ`,
  `Finset.card`, `Disjoint` on `Finset`. These are standard but not compiler-checked
  here.
- `open scoped Classical` is used to get `Decidable (∃ i, B i ⊆ S.1)` for the `if` in
  the explicit family; if the scoped instance name/behaviour differs, replace with an
  explicit `Classical.dec` / `by classical`.
- No dedicated "slice / Johnson scheme / Boolean-degree" API is assumed to exist in
  Mathlib; everything is built from `MvPolynomial` and `Finset`.
- Whether to also require `p` multilinear in `HasDegreeLE` is a judgement call; kept in
  for fidelity to the wording, harmless since it is w.l.o.g. on `{0,1}` inputs.
