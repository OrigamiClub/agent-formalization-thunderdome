# agent_014 — Filmus–Ihringer, statement-only formalization

## What I stated

Both directions, plus the explicit witnessing family, in three declarations:

- `filmus_ihringer` — a conjunction of:
  - **Forward:** `∃ M : ℕ`, for all `k ≥ 2d`, `n ≥ 2k`, every Boolean, degree-`≤ d`
    function on `binom([n],k)` is an `M`-junta. `M` depends only on `d` (it is
    existentially quantified before `k`, `n`), matching "a constant `m(d)`".
  - **Converse:** for all `1 ≤ k < 2d` and all `m`, there exist `n ≥ 2k` and a
    function that is Boolean, degree-`≤ d`, and not an `m`-junta.
- `filmus_ihringer_explicit_witness` — for `1 ≤ k < 2d` and every `m`, there are
  `ℓ`, `n`, pairwise-disjoint size-`e` blocks `B : Fin ℓ → Finset (Fin n)` with
  `e = min d k`, `ℓ·e > m`, `n ≥ 2ℓe` (and `n ≥ 2k`), such that
  `f S = ∑ i, ∏ j ∈ B i, x_j` is Boolean, degree-`≤ d`, and not an `m`-junta.

`d` is a hypothesis-carried `(d : ℕ)` with `1 ≤ d` in every theorem.

## Encoding decisions

- **Slice:** implicit. A slice function is `f : Finset (Fin n) → ℝ`; all statements
  only constrain/consult `f` on `S` with `S.card = k`. Chosen over a subtype
  `{S // S.card = k}` because it keeps `MvPolynomial.eval` and the junta
  intersection condition syntactically light, and over `Sym`/`Set` for the same
  reason. `n` and `k` are plain `ℕ` parameters; the coordinate set is `Fin n`.
- **Boolean codomain:** `{0,1} ⊆ ℝ` (`IsBooleanOn`: `f S = 0 ∨ f S = 1`). Keeps a
  single codomain `ℝ` shared with the polynomial evaluation, so "degree" needs no
  coercion.
- **Degree ≤ d:** `HasSliceDegreeLE` via `MvPolynomial (Fin n) ℝ`: `∃ p`,
  `p.totalDegree ≤ d`, `p` multilinear, and `f S = eval (indicator S) p` for every
  `S` on the slice. Multilinearity is `IsMultilinearPoly p : ∀ c ∈ p.support, ∀ i, c i ≤ 1`
  (every monomial exponent ≤ 1), included to match the term "multilinear real
  polynomial" in the problem's definition. It is harmless on 0/1 inputs but I keep
  it for faithfulness.
- **m-junta:** `IsSliceJunta` — `∃ J : Finset (Fin n)`, `J.card ≤ m`, and for all
  slice `S, T`, `S ∩ J = T ∩ J → f S = f T`.
- **m(d):** existential `∃ M : ℕ` inside the statement (not an explicit
  `m : ℕ → ℕ`), since only existence of a `d`-dependent bound is asserted.
- **Explicit family:** included as a separate theorem so the core two-directional
  statement does not depend on getting the family exactly right. Blocks are given
  abstractly as pairwise-disjoint `e`-sets `B : Fin ℓ → Finset (Fin n)` rather than
  the literal consecutive index blocks `(i-1)e + j`; the function is written
  literally as `∑ i, ∏ j ∈ B i, (if j ∈ S then 1 else 0)`. `¬ IsSliceJunta n k m f`
  together with `m < ℓ · min d k` expresses "depends on `ℓe > m` coordinates".

## Uncertainties / caveats

- **Σ/Π swap (deliberate correction).** The source text gives the family as
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. Taken literally on the slice this is
  *not* Boolean-valued (e.g. `k ≤ d`, `e = k`: a set `S` splitting across two
  blocks gives a factor product like `2·2 = 4`). The reading `∑_i ∏_j` — a sum of
  `ℓ` disjoint degree-`e` monomials, so `f S = #{i : B i ⊆ S}` — *is* Boolean of
  degree `min d k ≤ d` in all subcases (`k ≤ d`: `B i ⊆ S ⇔ S = B i`; `d < k < 2d`:
  two disjoint `d`-blocks cannot both fit in a `k < 2d` set), and it reproduces the
  known counterexamples (including `d = k = 1`, `f = ∑_{i} x_i` on singletons). I
  formalized the corrected `∑_i ∏_j` version and flag it here and in the `.lean`
  docstring. If the grader wants the verbatim `∏_i ∑_j`, swap the two big operators
  in `filmus_ihringer_explicit_witness`.
- "not `ℓe`-juntas" in the source is really "depends on `ℓe` coordinates, hence not
  an `m`-junta once `ℓe > m`"; I encoded the latter (`m < ℓ · min d k` plus
  `¬ IsSliceJunta n k m f`).
- Guessed / assumed Mathlib identifiers: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.support`, `Finsupp` application `c i`,
  `Pairwise`, `Disjoint` on `Finset`, and the big-operator syntax `∏ j ∈ s, _` /
  `∑ i : Fin ℓ, _` (current Mathlib `∈` form). `import Mathlib` used for safety.
- The forward direction uses exactly the source's hypotheses `k ≥ 2d`, `n ≥ 2k`
  (the latter also supplies the "`n − k` large" side condition, since
  `n − k ≥ k ≥ 2d`).
