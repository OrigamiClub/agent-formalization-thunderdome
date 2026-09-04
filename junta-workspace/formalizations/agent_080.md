# Agent 080 — formalization note

## What is stated

Statement only; every theorem ends `:= by sorry`.

1. `filmus_ihringer (d : ℕ) (hd : 1 ≤ d)` — **both directions** as a
   conjunction:
   - Forward: `∃ M : ℕ, ∀ n k, 2*d ≤ k → 2*k ≤ n → ∀ f, IsBoolean f →
     HasDegreeLE d f → IsJunta M f`. The junta constant `m(d)` is an
     existential over `ℕ` chosen before `k, n, f`.
   - Converse: `∀ k, 1 ≤ k → k < 2*d → ∀ m, ∃ n, 2*k ≤ n ∧ ∃ f, IsBoolean f ∧
     HasDegreeLE d f ∧ ¬ IsJunta m f`. `k` is universally quantified inside the
     regime `[1, 2d)`; the counterexample function is existential here.

2. `filmus_ihringer_explicit_family` — the explicit witnessing family, stated
   separately: for `e = min d k` and `n ≥ 2·ℓ·e`, the function got by evaluating
   `blockProduct e ℓ` on the slice is Boolean, degree `≤ d`, and not an
   `ℓ·e`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := { S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k }`.
  Natural-number coordinates (not `Fin n`) so that a single polynomial ring
  `MvPolynomial ℕ ℝ` serves all `n`, and the explicit family
  `∏_i ∑_j X (i*e+j)` needs no `Fin n` bound proofs. `abbrev` keeps it reducible
  so subtype projections `S.1 / S.2` and dot notation work.
- **Boolean codomain**: functions are `Slice n k → ℝ` plus a separate
  `IsBoolean` hypothesis (`∀ S, f S = 0 ∨ f S = 1`). Keeping the codomain `ℝ`
  makes "agrees with a real polynomial" statable directly without a coercion
  layer.
- **Degree ≤ d**: `HasDegreeLE d f` = `∃ p : MvPolynomial ℕ ℝ`, `IsMultilinear p`
  (self-defined: every exponent in every support monomial is `≤ 1`),
  `p.totalDegree ≤ d`, and `∀ S, f S = eval (indicatorVec S) p`. I included
  multilinearity because the theorem text says "multilinear real polynomial";
  on `0/1` inputs it is WLOG, so dropping it would give an equivalent notion.
- **m-junta**: `IsJunta m f` = `∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T,
  S.1 ∩ J = T.1 ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`"
  formulation restricted to the slice's own points (comparisons are between two
  slice elements, not arbitrary sets).
- **m(d)**: existential `∃ M : ℕ` inside the statement rather than an explicit
  `m : ℕ → ℕ`.
- `blockProduct e ℓ : MvPolynomial ℕ ℝ` is
  `∏ i ∈ range ℓ, ∑ j ∈ range e, X (i*e + j)` — the 0-based reindexing of
  `∏_{i=1}^{ℓ} Σ_{j=1}^{e} x_{(i-1)e+j}`.

## Uncertainties / caveats

- Mathlib identifiers used: `MvPolynomial.support`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X`, `Finset.range`, `Finset.card`,
  big-operator `∏ / ∑ … ∈ …` syntax. These are standard and I am fairly
  confident, but I have no compiler here. `IsMultilinear` / `IsBoolean` /
  `IsJunta` / `HasDegreeLE` are all defined locally in the file's namespace, so
  no name-collision risk.
- `MvPolynomial.eval` is applied as `MvPolynomial.eval v p`; if the exact form
  in the installed Mathlib is `(MvPolynomial.eval v) p` via an `AlgHom` coercion
  it is still syntactically the same application.
- The explicit family (`filmus_ihringer_explicit_family`) is transcribed
  literally from the problem's formula, with only the stated hypotheses
  (`1 ≤ k`, `k < 2*d`, `e = min d k`, `n ≥ 2*ℓ*e`). I was not able to fully
  reconstruct the paper's construction, and the literal product
  `∏_i (Σ_{j∈B_i} x_j)` read naively has polynomial degree `ℓ` (not `d`) and can
  collapse to a constant on a fixed-`k` slice when `ℓ` is large. The paper
  presumably (a) computes the *slice* degree after reduction modulo
  `Σ x_i = k`, and/or (b) imposes further relations among `ℓ, e, k` (and lets
  `k` scale) that I have not encoded. I kept the clause because the task invites
  including the family, but its side conditions may be incomplete/too weak as
  stated; the mathematical content of the theorem lives in `filmus_ihringer`.
- The forward direction quantifies `n, k` after choosing `M`; I read
  "there is a constant m(d)" as this uniform existential.
