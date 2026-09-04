# agent_083 — formalization note

## What is stated

All three parts, as separate `theorem … := by sorry`:

1. `boolean_degree_d_on_slice_is_junta` — positive direction: `∃ m : ℕ → ℕ` such
   that `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`, `f` Boolean of degree `≤ d` ⇒ `f` is an
   `m d`-junta.
2. `boolean_degree_d_on_slice_junta_bound_sharp` — converse, abstract form: for
   `1 ≤ k < 2d` and every `m`, there exist `n ≥ 2k` and a Boolean degree-`d`
   function on the slice that is not an `m`-junta.
3. `boolean_degree_d_on_slice_sharp_witness` — the same converse with the
   explicit family exhibited (`witnessPoly` / `witnessFun`).

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)` — direct match for `{S ⊆ [n] : |S| = k}`, and `.1` projection
  works because it is an `abbrev` (reducible).
- **Boolean codomain**: functions `Slice n k → ℝ` together with the side
  predicate `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`
  so that "degree" can be phrased directly against a real polynomial with no
  coercion bookkeeping.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`,
  `p.totalDegree ≤ d` and `f` agrees on the whole slice with
  `MvPolynomial.eval (indicatorVec S.1) p`, where `indicatorVec` is the `0/1`
  indicator in `ℝ^n`. The polynomial is drawn from the full `MvPolynomial` ring
  (not restricted to multilinear): this is the standard convention — the degree
  of `f` is the least `d` admitting such a `p`, and e.g. `X i ^ 2 = X i` on `0/1`
  so nothing is lost by allowing non-multilinear representatives.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m` and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` ("value depends only on `S ∩ J`").
- **m(d)**: an explicit `∃ m : ℕ → ℕ` at the head of the positive statement
  (existential inside the theorem), matching "there is a constant `m(d)`".
- **Parameters** `n, k, d, m` are plain `ℕ` arguments; the ambient coordinate set
  is `Fin n`.

## The explicit family and its deviation from the prompt

The prompt writes the witnesses as `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with
`e = min(d,k)`. I formalized the **sum-of-products** shape instead:
`∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} X_{i·e+j}` (`witnessPoly`).

Reason: the product-of-sums polynomial has total degree `ℓ`, which is unbounded
as `ℓ → ∞`, so it cannot simultaneously have slice-degree `≤ d` and be driven to
"not an `m`-junta" by taking `ℓ` large. The sum-of-products form has total degree
`e = min(d,k) ≤ d`; when `1 ≤ k < 2d` one gets `k < 2·min(d,k)`, so any `k`-set
contains at most one full block and the sum is `0/1`-valued (Boolean); and it
genuinely depends on all `ℓ·e` block coordinates, so it is not an `m`-junta once
`ℓ·e > m`. I read the prompt's "`∏_i ∑_j`" as a transposition of "`∑_i ∏_j`".

"which … are not `ℓe`-juntas" is rendered as: for every `m`, picking `ℓ` with
`ℓ · min d k > m`, the function is not an `m`-junta (its essential-coordinate
count is `ℓ·e`, made larger than any prescribed `m`).

Out-of-range coordinate indices in `witnessPoly` are sent to `0` via `dite`; the
size hypothesis `2·(ℓ · min d k) ≤ n` guarantees every actual term uses a valid
`Fin n` index (`i·e+j ≤ ℓ·e − 1 < n`).

## Uncertainties / guessed identifiers

- Mathlib identifiers used: `MvPolynomial`, `MvPolynomial.eval`,
  `MvPolynomial.X`, `MvPolynomial.totalDegree`. These are standard and I am
  fairly confident of the names and signatures; `eval` takes the point as its
  first explicit argument (`eval (f : σ → R) : MvPolynomial σ R →+* R`).
- I am not aware of any native Mathlib notion of "Boolean degree-`d` function on
  a slice" or "slice junta", so `HasSliceDegreeLE` and `IsJunta` are defined from
  scratch.
- The exact value/growth of `m(d)` is left fully abstract (existential); the
  paper's bound is roughly exponential in `d`, but the statement only claims
  existence of some `m : ℕ → ℕ`.
- `min d k` is `Nat.min`; with `d ≥ 1` and `k ≥ 1` it is `≥ 1`.
