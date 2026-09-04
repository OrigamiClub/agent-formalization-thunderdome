# Agent 003 — formalization note

## What I stated

- **`filmus_ihringer`**: BOTH directions, as a conjunction.
  - Positive: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f` Boolean of slice-degree `≤ d`
    on `binom([n],k)`, `f` is an `m`-junta.  `m(d)` is an **existential inside the
    statement** (`∃ m : ℕ`), matching "there is a constant m(d)".
  - Converse: `∀ d ≥ 1, ∀ k, 1 ≤ k < 2d, ∀ m, ∃ n ≥ 2k, ∃ f` Boolean of
    slice-degree `≤ d` that is **not** an `m`-junta.
- **`filmus_ihringer_lower_explicit`**: the explicit witnessing family for the
  converse, stated separately so the main theorem stays clean.

## Encoding decisions

| Choice | Encoding | Why |
|---|---|---|
| Slice `binom([n],k)` | `Slice n k := {S : Finset (Fin n) // S.card = k}` | Direct, easy to intersect with a junta set `J`; `Fin n` is the ambient coordinate set. |
| Boolean codomain | `f : Slice n k → ℝ` with `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1` | Real codomain is needed anyway for "degree via a real polynomial"; the predicate keeps `f` a genuine `{0,1}`-function without a separate `Bool`/`ℝ` coercion layer. |
| Degree `≤ d` | `HasSliceDegreeLE f d`: `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`, `∀ i, p.degreeOf i ≤ 1` (multilinear), and `∀ S, f S = eval (indicator S) p`, where `indicator S i = if i ∈ S then 1 else 0`. | Follows the "Terms" paragraph literally: agrees on the slice with a multilinear real polynomial of total degree `≤ d` evaluated at the 0/1 indicator vector. |
| `m`-junta | `IsJunta f m`: `∃ J : Finset (Fin n)`, `J.card ≤ m`, `∀ S T, S ∩ J = T ∩ J → f S = f T`. | "Value depends only on `S ∩ J`" for a `≤ m`-coordinate set `J`. |
| `n`, `k`, `d` | Plain `ℕ` arguments; hypotheses `1 ≤ d`, `2*d ≤ k`, `2*k ≤ n`, `1 ≤ k`, `k < 2*d` written inline. | Keeps the statement first-order and self-contained. |
| Explicit family | Included as a separate theorem. `block n e i` = coordinates in `[i·e, i·e+e)` of `Fin n` (via `Finset.univ.filter`, no side proofs). `explicitPoly n e ℓ = ∑_{i<ℓ} ∏_{x ∈ block i} X x`. `explicitBoolFn d k n ℓ S = if ∃ i < ℓ, block i ⊆ S then 1 else 0`, with `e = min d k`. | Matches the corrected formula `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` from Filmus arXiv:2203.04760 (see uncertainties). |

The explicit theorem asserts: `explicitBoolFn` is Boolean; equals `eval (indicator ·) (explicitPoly …)` on the slice; that polynomial is multilinear with `totalDegree ≤ d`; hence `HasSliceDegreeLE … d`; and it is not an `m`-junta for any `m < ℓ·e`.  Hypotheses `2·(ℓ·e) ≤ n` and `2k ≤ n`.

## Uncertainties

- **The witness formula in the TASK prompt appears garbled.**  It reads
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` ("product of block sums"), but that is
  *not* Boolean on the slice for `k ≥ 2` (an `S` with two elements in one block and
  one in each other gives value `≥ 2`), and has apparent degree `ℓ`, not `≤ d`.
  A web search surfaced the form `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` ("sum of
  block monomials") from Filmus, "Junta threshold for low degree Boolean functions
  on the slice" (arXiv:2203.04760).  That version *is* degree `e = min(d,k) ≤ d`,
  and is Boolean precisely because `k < 2d` forbids two disjoint `e`-blocks inside
  a `k`-set.  I formalized the sum-of-monomials version.
- **"not `ℓe`-juntas".**  As written this is literally false for the
  sum-of-monomials witness: a function whose relevant variables are exactly the
  `ℓe` block coordinates *is* an `ℓe`-junta.  I read the intended content as "its
  minimal junta has `ℓe` coordinates", i.e. it is not an `m`-junta for any
  `m < ℓe`; since `ℓ` is unbounded this is what defeats a fixed `m(d)`.  Stated as
  `∀ m < ℓ·e, ¬ IsJunta … m`.
- **Guessed Mathlib identifiers** (not compiler-checked): `MvPolynomial`,
  `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`, `MvPolynomial.eval`,
  `MvPolynomial.X`, `Finset.univ.filter`, `Finset.range`, `Finset.sum`/`prod`
  notation `∑ … ∈ …, ` / `∏ … ∈ …, `.  API names/argument orders may need
  adjustment (e.g. `Finset.filter` argument order, `degreeOf` vs `degreeOf i p`).
- Multilinearity in `HasSliceDegreeLE` is included for faithfulness to the "Terms"
  wording; it is WLOG on the slice and could be dropped without changing the class
  of functions.
- `IsJunta` is phrased for the real-valued `f`; combined with `IsBoolean` it is the
  usual notion.  I did not use a Mathlib `Function.Junta`-style definition (I am not
  confident one exists for this setting).
