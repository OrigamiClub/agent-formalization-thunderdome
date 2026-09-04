# Agent 073 — formalization note

## What I stated

Three `sorry`-terminated theorems in namespace `FilmusIhringer`:

1. `boolean_degree_d_is_junta` — the **forward direction**. For `d ≥ 1` there
   exists `m : ℕ` such that for all `k ≥ 2d`, all `n ≥ 2k`, every Boolean
   degree-`d` function on the slice is an `m`-junta.
2. `exists_boolean_degree_d_not_junta` — the **converse**, in clean existence
   form: for `1 ≤ k < 2d` and every `m`, some slice `binom([n],k)` with `n ≥ 2k`
   carries a Boolean degree-`d` function that is not an `m`-junta. This statement
   does not depend on the explicit construction.
3. `blockFun_not_junta` — the **explicit witnessing family**
   `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, claiming Boolean +
   degree `≤ d` + not an `ℓe`-junta whenever `1 ≤ k < 2d`, `ℓ ≥ 1`, `n ≥ 2ℓe`.

I included the explicit family because the task supplied it; theorem 2 is kept
independent of it so the converse survives even if the family transcription is
imperfect (see uncertainties).

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Simplest faithful
  choice; ambient coordinate set is `Fin n`. `n, k, d` are ordinary `ℕ`
  arguments/binders; `m(d)` is an **existential inside** the forward statement
  (no explicit `m : ℕ → ℕ`), matching "there is a constant `m(d)`".
- **Boolean codomain**: functions are `Slice n k → ℝ`, with a separate predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Real-valued is forced by the degree
  notion (real polynomials), so a `{0,1} ⊆ ℝ` encoding is the least friction.
- **Degree ≤ d**: `HasDegreeLE d f` = existence of `p : MvPolynomial (Fin n) ℝ`
  with `p.totalDegree ≤ d`, multilinear (`∀ s ∈ p.support, ∀ i, s i ≤ 1`), and
  `f S = MvPolynomial.eval (indicator S) p` on every slice point. This is the
  standard "agrees on the slice with a low-degree polynomial" definition; the
  minimal degree over representations is not separately named.
- **indicator**: `fun v => if v ∈ (S : Finset (Fin n)) then 1 else 0`.
- **m-junta**: `IsJunta m f` = `∃ J, J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
  Captures "value depends only on `S ∩ J`".
- **Explicit family**: `blockPoly e ℓ n : MvPolynomial (Fin n) ℝ` built as
  `∏ i ∈ range ℓ, ∑ v ∈ univ.filter (i*e ≤ v < i*e+e), X v`. Using a `filter` over
  `Fin n` avoids any `Fin.mk` bound-proof obligations (no proof content sneaks
  into the statement); when `n ≥ ℓe` the blocks are genuine size-`e` disjoint
  intervals. Indexing is `0`-based (`i ∈ {0,…,ℓ-1}`, coords `{i·e,…,i·e+e-1}`),
  a relabelling of the task's 1-based `(i-1)e+j`. The junta threshold is kept at
  `ℓ * min d k` exactly as written.

## Uncertainties

- **Guessed Mathlib identifiers**: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X`, `(p : MvPolynomial _ _).support` with
  elements `Fin n →₀ ℕ` and `s i : ℕ`, `Finset.range`, `Finset.filter` via
  `s.filter p` dot-notation, big-operator notation `∏ / ∑ ... ∈ ...`. I believe
  these are current, but did not run a compiler. `noncomputable` is marked on the
  `MvPolynomial`-valued/using defs defensively.
- **Literal transcription of the family**: I rendered the inner operation as a
  genuine sum `Σ x_j` per the task text. Under a strict reading, `∏_i (Σ_j x_j)`
  evaluated on a `k`-set is `∏_i |S ∩ B_i|`, which is `0` unless all `ℓ` blocks
  are hit (forcing `ℓ ≤ k`) and need not be `{0,1}`-valued; for the family to be
  Boolean and to depend on unboundedly many coordinates as `ℓ → ∞`, the inner
  `Σ` is presumably intended as "block `i` is hit" (a disjunction), with
  Boolean-ness / degree `≤ d` on the slice relying on `k < 2d`. I kept the
  literal sum and flag this; theorem 3's stated conclusion should be read as the
  intended construction rather than a claim about the literal polynomial.
- **`ℓe` vs `ℓe − 1` junta threshold**: the literal function depends on exactly
  `ℓe` coordinates, so it is trivially an `ℓe`-junta; "not an `ℓe`-junta" as
  phrased in the task is likely an off-by-one or reflects a slightly larger
  construction. I preserved the task's `ℓ * min d k` threshold verbatim.
- **Symmetric size condition**: I used `n ≥ 2k` (which gives `n − k ≥ k ≥ 2d`) as
  the sole largeness hypothesis in the forward direction, matching the task.
