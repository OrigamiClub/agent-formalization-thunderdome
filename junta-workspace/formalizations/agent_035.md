# Agent 035 — formalization note

## Source

The precise statement to formalize is **Theorem 1.1** of

> Yuval Filmus, *Junta threshold for low degree Boolean functions on the slice*,
> arXiv:2203.04760v2 (2022),

which is the sharp form of the Filmus–Ihringer result
*Boolean constant degree functions on the slice are juntas*
(Discrete Math. 342 (2019), 111614). I checked both papers directly.

## What I stated

I stated **both directions** of Theorem 1.1, plus the **explicit witnessing
family** for the sharpness direction, in three declarations:

1. `filmus_junta_threshold` — the full Theorem 1.1 as a single statement:
   `∃ m`, (threshold direction) `∧` (sharpness direction), under `d ≥ 1`.
   * threshold: `2*d ≤ k → 2*k ≤ n → IsBoolean f → HasDegreeLE f d → IsJunta f m`;
   * sharpness: `1 ≤ k → k < 2*d → ∀ M, ∃ n ≥ 2*k, ∃ f, Boolean ∧ degree ≤ d ∧ ¬ M-junta`.
   The sharpness conjunct is kept abstract (matching the paper's "Conversely, …"),
   and it does not refer to `m`; nesting it under `∃ m` is harmless and mirrors
   the paper's phrasing "There exists a constant m(d) such that … . Conversely …".

2. `witness` — the explicit family
   `∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i·e+j}` evaluated at the indicator vector of a
   slice point, on coordinates `0 … ℓe-1`, with `e = min d k`.

3. `filmus_witness_family` — for `1 ≤ k < 2d`, `e = min d k`, `ℓ ≥ 1`,
   `n ≥ 2ℓe`: `witness` is Boolean, has degree `≤ d`, and is not an
   `(ℓe − 1)`-junta.

## Encoding decisions

* **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}` — a `k`-subset of
  `Fin n`, identifying a weight-`k` point of `{0,1}^n` with its support. Chosen
  over `Sym`/`Set`/raw `Finset (Finset …)` because `Finset.card`, `∩`, and
  membership give the cleanest junta and indicator statements.
* **Boolean codomain**: functions are `Slice n k → ℝ`, with a separate predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. This matches the paper verbatim
  ("A Boolean function is a `{0,1}`-valued function", values in `ℝ`) and keeps
  the polynomial/degree notion over `ℝ` without coercions.
* **Degree ≤ d**: `HasDegreeLE f d := ∃ P : MvPolynomial (Fin n) ℝ,
  P.totalDegree ≤ d ∧ ∀ S, f S = MvPolynomial.eval (ind S) P`, where
  `ind S i = if i ∈ S then 1 else 0`. This is exactly the paper's *alternative*
  characterization ("minimum degree of a real polynomial, not necessarily
  multilinear or harmonic, agreeing with `f` on the slice"). I deliberately did
  **not** impose multilinearity (`degreeOf ≤ 1`) or harmonicity
  (`∑ ∂P/∂xᵢ = 0`): the paper proves these can always be arranged and its own
  headline definition uses the plain-polynomial version. No Mathlib "slice
  degree" notion exists.
* **m-junta**: `IsJunta f m := ∃ J : Finset (Fin n), J.card ≤ m ∧
  ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` — "`f` factors through `S ↦ S ∩ J`",
  the ∀-form of the paper's "`f(x) = g(x|_J)` for some `g : {0,1}^J → ℝ`,
  `|J| ≤ m`".
* **`m(d)`**: existential *inside* the statement (`∃ m : ℕ, …`), with `d` a
  fixed variable and `hd : 1 ≤ d`. Matches "There exists a constant m(d)".
* **`n, k, d` and coordinates**: `d` fixed at top level; `k, n` universally
  quantified inside each direction; ambient coordinate type `Fin n`. The witness
  uses coordinates `0 … ℓe-1` of `Fin n` via a dependent `if h : i*e+j < n`
  guard (the hypothesis `n ≥ 2ℓe` makes the guard always true, but stating it
  this way keeps `witness` total for all arguments).
* **Explicit family indexing**: `witness n k e ℓ` with `e` a separate parameter,
  instantiated to `min d k` in `filmus_witness_family`. Blocks are the disjoint
  ranges `{i·e, …, i·e+e-1}` for `i = 0 … ℓ-1`.

## Uncertainties / caveats

* **Prompt vs. paper on the witness family.** The task prompt writes the
  witnesses as a **product of sums**
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. The paper (arXiv:2203.04760, p. 1
  and the converse proof on p. 5, e.g. `f = a + (b-a) ∑ x_{{(i-1)k+1,…,ik}}`)
  uses a **sum of products** `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`. Only the
  sum-of-products form is `{0,1}`-valued on `binom([n],k)` when `k < 2e` (each
  disjoint size-`e` block lies in `S` for at most one `i`), which is what makes
  it a *Boolean* degree-`d` function. I therefore formalized the
  **sum-of-products** form. I also read the paper's intro index `(e-1)i+j` as a
  typo for `(i-1)e+j` (disjoint blocks), consistent with its own converse proof;
  I used disjoint blocks `i·e + j`, 0-based.
* **"not `ℓe`-juntas".** The paper's remark literally says the witnesses "are
  not `ℓe`-juntas", but the function depends only on `ℓe` coordinates, so it
  *is* an `ℓe`-junta; the sharp claim provable from the paper's Lemma 2.2 is
  "not an `(ℓe − 1)`-junta". I stated `¬ IsJunta … (ℓ * min d k - 1)`.
* **Guarded `ℓ ≥ 1`.** For `ℓ = 0` the witness is the empty sum `0` (a junta)
  and `ℓe - 1` underflows in `ℕ`; I added `hℓ : 1 ≤ ℓ`.
* **Mathlib identifiers** used (believed current): `MvPolynomial`,
  `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `Finset.range`, `Finset.sum`
  / `Finset.prod` with `∑ _ ∈ _,` / `∏ _ ∈ _,` notation, `Finset.card`,
  `Finset.instInter`, `min` on `ℕ`. `import Mathlib` (whole library) for safety.
* I did **not** formalize the `A`-valued generalization (Thm 1.2), the infinite
  slice (Thm 1.3), or the explicit form of `m(d)` — the prompt's theorem is the
  Boolean case with `m(d)` existential.
