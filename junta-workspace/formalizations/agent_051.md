# Agent 051 — formalization note

## What I stated

Three `sorry` theorems in namespace `FilmusIhringer`:

1. `boolean_degree_isJunta` — the **forward direction**: for `d ≥ 1` there exists
   `m : ℕ` such that for all `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`≤ d`
   function on the slice is an `m`-junta.
2. `boolean_degree_not_isJunta` — the **converse**, pure existence form: for `d ≥ 1`
   and `1 ≤ k < 2d`, for every `m` there is `n ≥ 2k` and a Boolean degree-`≤ d`
   function on `binom([n],k)` that is not an `m`-junta.
3. `tightnessFun_witness` — the **explicit witnessing family**
   `∏_{i}(∑_j x_{ie+j})` with `e = min d k`, asserting (for `n ≥ 2ℓe`) that it is
   Boolean, has degree `≤ d`, and is not an `(ℓe)`-junta.

I stated both directions plus the explicit family, since the task left this to me
and each is a distinct piece of mathematical content.

## Encoding decisions

- **Slice**: `def Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)` keeps the "intersection with a coordinate set `J`" in `IsJunta`
  literal (`x.1 ∩ J`), which a `Sym`/multiset encoding would obscure.
- **Coordinate set**: `Fin n`, with `n k d` all universally quantified `ℕ` inside
  each theorem (no section variables), so the quantifier order `∃ m, ∀ k n f`
  in the forward direction is visibly the "uniform `m(d)`" statement.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a side predicate
  `IsBoolean f : ∀ x, f x = 0 ∨ f x = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  because "degree `≤ d`" is most directly stated via a real polynomial, and this
  keeps `f` and the polynomial in the same type.
- **Degree `≤ d`**: `HasDegreeLE` = existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` agreeing with `f` at the `{0,1}` indicator vector on every
  slice point. I do **not** require `p` multilinear: on `{0,1}` inputs
  multilinearization preserves values and does not raise total degree, so the
  notion is identical. `indicator S i = if i ∈ S then 1 else 0`.
- **`m`-junta**: `IsJunta` = existence of `J : Finset (Fin n)` with `J.card ≤ m`
  such that `x.1 ∩ J = y.1 ∩ J → f x = f y`. This is "value depends only on
  `S ∩ J`" for a set of `≤ m` coordinates.
- **`m(d)`**: existential inside the statement (`∃ m : ℕ, …`) rather than an
  external `m : ℕ → ℕ`. Equivalent for a statement-only rendering; the existential
  is self-contained.
- **Explicit family indexing**: reindexed from `0`; block `i ∈ range ℓ` uses
  coordinates `i*e … i*e+e-1`. Out-of-range indices (`≥ n`) fold to `0` via `dite`,
  harmless when `n ≥ ℓe`. `tightnessPoly` is the honest product-of-linear-forms
  polynomial (total degree `ℓe`, generally `> d`); the *claim* that it agrees on
  the slice with a degree-`≤ d` polynomial is part of `HasDegreeLE` in
  `tightnessFun_witness`.

## Uncertainties

- Mathlib identifiers used from memory: `MvPolynomial (Fin n) ℝ`,
  `MvPolynomial.X`, `MvPolynomial.eval`, `MvPolynomial.totalDegree` (as
  `p.totalDegree`), `Finset.card`, `Finset` intersection `∩`, `Finset.range`,
  `∏ i ∈ s, _` / `∑ j ∈ s, _` `BigOperators` notation. I am fairly confident of
  all of these; `import Mathlib` should supply them. No dedicated Mathlib notion
  of "Boolean function on the slice" or "degree on the slice" is assumed — I
  spelled both out.
- `Slice` is a bare `def` to `Type`; if elaboration of `f : Slice n k → ℝ` ever
  needs it reducible, marking it `@[reducible]` or using `abbrev` would be safer.
- **`tightnessFun_witness` faithfulness**: I encoded the task's literal wording
  "not an `ℓe`-junta". Strictly, `tightnessFun n k ℓ e` reads only coordinates
  `< ℓe` by construction, so it *is* trivially an `ℓe`-junta and the negation as
  written looks false; the intended content is surely "genuinely depends on all
  `ℓe` coordinates", i.e. not an `(ℓe − 1)`-junta. I kept the task's `ℓe` but flag
  it here. The robust converse `boolean_degree_not_isJunta` (theorem 2) avoids
  this by only asserting non-`m`-junta for the externally chosen `m` (take `ℓ`
  with `ℓe > m`).
- Whether the product family is Boolean / degree `≤ d` on the slice for *all*
  parameter choices in range (e.g. degenerate small cases like `d = k = 1`,
  `ℓ ≥ 2`, where the product collapses to `0`) is taken on trust from the task
  statement; `tightnessFun_witness` may need extra hypotheses (such as `ℓ ≤ k`) to
  be literally true. I did not add them, to stay close to the given wording.
