# Agent 054 — formalization note

## What I stated

Three `sorry`-terminated theorems in `namespace FilmusIhringer`:

1. `boolean_degree_junta` — **forward direction**. `∀ d ≥ 1, ∃ m, ∀ k n, 2d ≤ k → 2k ≤ n →`
   every Boolean degree-`d` `f` on the slice is an `m`-junta. `m(d)` is an existential
   *inside* the statement (matches "there is a constant m(d)").
2. `boolean_degree_not_junta` — **converse, existential form**. For `d ≥ 1`, `1 ≤ k < 2d`,
   and every `m`, there is `n ≥ 2k` and a Boolean degree-`d` function on the slice that
   is not an `m`-junta.
3. `boolean_degree_not_junta_explicit` — **converse with the explicit family**
   `∏_{i}(∑_{j} x_{i·e+j})`, `e = min d k`. Literal transcription; caveats below.

## Encoding decisions

- **Slice**: `abbrev Slice (n k) := { S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k }`.
  Chose `Finset ℕ` over `Finset (Fin n)` so that the explicit family's index arithmetic
  `i·e + j` needs no `Fin` bound proofs; the `⊆ Finset.range n` clause carries the
  ambient coordinate set.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` with `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`.
  Keeps `f` in the same type as the polynomial evaluation used for degree.
- **Degree ≤ d**: `HasDegreeAtMost f d` = there is `p : MvPolynomial ℕ ℝ` that is
  `IsMultilinear` (every support monomial has all exponents `≤ 1`) with
  `p.totalDegree ≤ d` and `∀ S, f S = MvPolynomial.eval (ind S) p`, where
  `ind S i = if i ∈ S then 1 else 0`. Multilinearity is imposed to match the wording
  "multilinear real polynomial"; on the Boolean slice it is w.l.o.g. (reduce `xᵢ² = xᵢ`).
- **m-junta**: `IsJunta f m` = `∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
- **m(d)**: existential inside the statement rather than an explicit `m : ℕ → ℕ`.
- **n, k, d**: plain `ℕ` arguments; `d ≥ 1` as hypothesis `1 ≤ d`. Regime hypotheses
  `2*d ≤ k`, `2*k ≤ n` transcribed exactly as in the problem statement (I did not add a
  separate `n - k` largeness hypothesis, since `n ≥ 2k` already gives `n - k ≥ k ≥ 2d`).
- **Explicit family**: `familyPoly e ℓ = ∏ i ∈ range ℓ, ∑ j ∈ range e, X (i*e+j)` (0-indexed
  version of `∏_{i=1}^{ℓ} ∑_{j=1}^{e} x_{(i-1)e+j}`); `familyFun n k e ℓ S = eval (ind S) (familyPoly e ℓ)`;
  `e` instantiated as `min d k`. The theorem asserts, for every `m`, existence of `ℓ, n`
  with `ℓ·e > m`, `n ≥ 2k`, `n ≥ 2ℓe`, and `familyFun` Boolean, degree `≤ d`, and not an
  `(ℓ·e)`-junta.

## Uncertainties

- **Guessed / assumed Mathlib identifiers**: `MvPolynomial.totalDegree`, `MvPolynomial.eval`
  (as a coercible ring hom applied `eval (ind S) p`), `MvPolynomial.support` returning
  `Finset (ℕ →₀ ℕ)` with `c i : ℕ`, `MvPolynomial.X : ℕ → MvPolynomial ℕ ℝ`, big-operator
  notation `∏ i ∈ Finset.range ℓ, …`. I could not run a compiler.
- **The explicit family (`boolean_degree_not_junta_explicit`) is a literal transcription
  I could not reconcile.** As written, `familyPoly e ℓ` mentions only coordinates
  `{0,…,ℓe-1}`, so `familyFun` depends only on `S ∩ Finset.range (ℓe)` and *is* an
  `(ℓe)`-junta — contradicting the "not `ℓe`-juntas" clause. For `ℓ = 1`, `e ≥ 2` the
  value `|S ∩ block|` also ranges outside `{0,1}`, so `IsBoolean` looks false too. I
  believe the source description omits context or I misread the indexing (e.g. the blocks
  may be spread across `[n]`, or the intended low-degree object differs from the displayed
  product). I kept the theorem as a faithful transcription but flagged it; theorems 1 and 2
  are the robust content. A reader should treat theorem 3's hypotheses/conclusion as
  possibly vacuous or unprovable as literally stated.
- I did not include an explicit `m : ℕ → ℕ` witnessing family; `m(d)` is existential.
- Direction chosen: both directions, plus the explicit family (flagged).
