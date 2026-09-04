# Agent 094 — formalization note

## What I stated

Statement only, three `theorem … := by sorry`:

1. `filmus_ihringer_forward` — the forward direction. For `d ≥ 1` there **exists** `m : ℕ`
   such that for all `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`≤ d` function on the
   slice is an `m`-junta.
2. `filmus_ihringer_converse` — the converse in pure existential form. For `1 ≤ k < 2d` and
   every `m`, there exist `n ≥ 2k` and a Boolean degree-`≤ d` function on the slice that is
   not an `m`-junta.
3. `filmus_ihringer_converse_explicit` — the converse witnessed by the explicit family
   `∏_{i<ℓ} Σ_{j<e} x_{i·e+j}` with `e = min d k`. For every `m` there are `n, ℓ` with
   `n ≥ 2k`, `n ≥ 2·ℓ·e` and `ℓ·e > m` making `blockFun n k e ℓ` Boolean, degree `≤ d`,
   and not an `m`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`
  is the most direct rendering of `{S ⊆ [n] : |S| = k}` and gives easy access to `S.1` for
  set operations and polynomial evaluation.
- **Boolean codomain**: real-valued functions `f : Slice n k → ℝ` with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2` so that
  "agrees with a real polynomial" needs no coercion, and `{0,1} ⊆ ℝ` matches the source.
- **degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` that is multilinear
  (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), has `p.totalDegree ≤ d`, and satisfies
  `f S = MvPolynomial.eval (indicator S.1) p` for every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. This is the "agrees on the slice with a
  multilinear polynomial of total degree ≤ d evaluated at the 0/1 indicator vector"
  definition from the problem's Terms section. Multilinearity is included for faithfulness;
  it does not change the function class on {0,1}^n but pins down the representation.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
  Direct transcription of "value depends only on `S ∩ J`" with `|J| ≤ m`.
- **m(d)**: existential `∃ m : ℕ` inside `filmus_ihringer_forward` rather than an explicit
  `m : ℕ → ℕ`. The theorem is an existence statement about the bound; `d` is a fixed
  parameter so the `m` obtained already depends on `d`.
- **n, k, d, coordinates**: all carried as explicit `ℕ` arguments / bound variables; the
  ambient coordinate set is `Fin n`. Hypotheses `1 ≤ d`, `2*d ≤ k`, `2*k ≤ n`, `1 ≤ k`,
  `k < 2*d` are plain inequalities.
- **Explicit family**: `blockPoly n e ℓ = ∏_{i ∈ range ℓ} ∑_{j ∈ range e} X_{i*e+j}` in
  `MvPolynomial (Fin n) ℝ`, 0-based (`(i-1)e+j` becomes `i*e+j`). A variable with nat index
  `≥ n` is replaced by `0` via a dependent `if`; under `n ≥ 2·ℓ·e` this fallback never
  fires. `blockFun n k e ℓ S = eval (indicator S.1) (blockPoly n e ℓ)`.

## Deviations / interpretation choices

- The problem text says the witnesses "for `n ≥ 2ℓe` are not `ℓe`-juntas". Taken literally
  that is false for small `ℓ` (e.g. `ℓ = 1`: `blockFun` depends only on the first `e`
  coordinates, so it *is* an `e`-junta). I read the intended content as: the minimal junta
  size is exactly `ℓe`, so by choosing `ℓ` with `ℓe > m` the function is not an `m`-junta.
  `filmus_ihringer_converse_explicit` therefore asserts `m < ℓ·e` and `¬ IsJunta m (blockFun …)`,
  which is the statement actually needed for the converse and is defensible.
- I also kept the plain existential converse (`filmus_ihringer_converse`) as the
  encoding-independent headline in case the explicit family's phrasing is contested.

## Uncertainties (Mathlib identifiers guessed from memory)

- `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X`, `MvPolynomial.support`
  — names and signatures believed correct; `eval` is `(σ → R) → MvPolynomial σ R →+* R`,
  applied as a function here.
- Multilinearity via `∀ t ∈ p.support, ∀ i, t i ≤ 1` relies on `p.support : Finset (σ →₀ ℕ)`
  and the `Finsupp` coercion to a function. There is (to my knowledge) no
  `MvPolynomial.IsMultilinear` predicate in Mathlib, hence the explicit form.
- `∏ i ∈ Finset.range ℓ, …` / `∑ j ∈ Finset.range e, …` BigOperators notation with `∈`.
- `noncomputable` markers on `blockPoly` / `blockFun` because of `ℝ` and `MvPolynomial.eval`.
- `import Mathlib` (whole library) for a self-contained file.
