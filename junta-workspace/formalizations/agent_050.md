# Agent 050 — formalization note

## What I stated

All three parts, as separate `theorem … := by sorry`:

1. `boolean_degree_junta_of_large_slice` — the **upper bound** (forward direction):
   `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k, every Boolean degree-≤ d function on the slice
   is an M-junta`.  `M = m(d)` is an existential placed *after* `d` but *before* `k, n`,
   so it depends only on `d`, matching "there is a constant `m(d)`".

2. `exists_boolean_degree_not_junta` — **tightness, existential form**:
   `∀ d ≥ 1, ∀ k with 1 ≤ k < 2d, ∀ m, ∃ n ≥ 2k, ∃ f` Boolean, degree `≤ d`, not an
   `m`-junta.

3. `sliceWitness_spec` — **tightness with explicit witnesses**: the family
   `sliceWitness n e ℓ` with `e = min d k`, stated to be Boolean, degree `≤ d`, and not
   an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`.  Ambient coordinate set
  is `Fin n`; `n`, `k`, `d`, `m`, `ℓ` are all plain `ℕ` arguments to the theorems.
- **Codomain**: real-valued functions `Slice n k → ℝ` together with a predicate
  `IsBooleanOnSlice f := ∀ S, f S = 0 ∨ f S = 1`.  Chosen over `Bool`/`Fin 2` because
  the degree notion is about agreement with a *real* polynomial, so keeping the function
  real-valued avoids coercions in `HasDegreeLE`.
- **Degree ≤ d**: `HasDegreeLE f d` = there is `p : MvPolynomial (Fin n) ℝ` with
  `∀ i, p.degreeOf i ≤ 1` (multilinear), `p.totalDegree ≤ d`, and
  `∀ S, f S = MvPolynomial.eval (indicatorVec S) p`, where
  `indicatorVec S i = if i ∈ S.1 then (1:ℝ) else 0`.  The multilinearity clause is
  included to match the wording "multilinear real polynomial"; it is not essential
  (multilinearization does not raise total degree on `{0,1}` inputs), so a reader may
  drop `∀ i, p.degreeOf i ≤ 1` without changing the class of functions.
- **m-junta**: `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
  "Depends only on `S ∩ J`" is rendered as: equal intersections with `J` force equal
  values.
- **Explicit family indexing**: `blockFin n e i` is the `i`-th width-`e` block
  `{i·e, …, i·e+e-1} ⊆ Fin n`, defined by `Finset.filter` on `Finset.univ` (0-based, so
  no off-by-one proof obligations and the definition is total for all `n, e, i`).
  `sliceWitnessPoly n e ℓ = ∑_{i∈range ℓ} ∏_{x∈blockFin n e i} X x`.
  `sliceWitness n e ℓ` evaluates it at `indicatorVec`.

## Deviation from the source phrasing (important)

The task writes the witnesses as a **product of sums**
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min(d,k)`.  Read literally this has
polynomial degree `ℓ`, is generally **not** `{0,1}`-valued on the slice, and — because
at most `k` of the `ℓ` blocks can be met by a `k`-set — degenerates (identically `0`
for `ℓ > k`), so it cannot be "not an `m`-junta" for arbitrary `m`.

I formalized instead the **sum of products**
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, i.e. `∑_i [block i ⊆ S]`.  With `e = min(d,k)`
and `k < 2d` one has `2e > k`, so a `k`-set contains **at most one** of the disjoint
width-`e` blocks; hence this function is `{0,1}`-valued, it is a squarefree polynomial
of total degree `e ≤ d`, it depends on all `ℓ·e` block coordinates, and `ℓ` is
unbounded.  This is the reading consistent with every clause of the theorem
("Boolean", "degree `d`", "for every `m` … not an `m`-junta", "`n ≥ 2ℓe`"), so I
believe the source has `∏` and `∑` transposed.  I note it here rather than silently
"fixing" it.

## Interpretation choices / uncertainties

- "**not `ℓe`-juntas**" in the task: since the witness manifestly depends on exactly
  `ℓe` coordinates it *is* trivially an `ℓe`-junta; the intended content is that it is
  not an `m`-junta for any `m < ℓe` (every one of those coordinates is relevant).  I
  stated `∀ m < ℓ·e, ¬ IsJunta f m`.
- The upper-bound theorem carries the hypotheses `k ≥ 2d` and `n ≥ 2k` exactly as
  given; I did not add extra nondegeneracy hypotheses.
- **Guessed / assumed Mathlib identifiers** (not compiler-checked): `MvPolynomial`,
  `MvPolynomial.X`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `MvPolynomial.degreeOf`, `Finset.filter` (predicate-then-set argument order,
  `DecidablePred` found by instance search), `Finset.range`, `Finset.univ`, the
  `∑ x ∈ s, _` / `∏ x ∈ s, _` `BigOperators` notation, and the `Fin n → ℕ` coercion
  `(x : ℕ)`.  All are standard, but exact names/signatures were written from memory.
- No Mathlib "Boolean degree on the slice" or "junta" notion is assumed to exist; I
  defined both.
