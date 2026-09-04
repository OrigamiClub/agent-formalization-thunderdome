# Agent 097 — formalization note

## Source pinned

The task's statement is verbatim **Theorem 1.1** of

> Yuval Filmus, *Junta threshold for low degree Boolean functions on the slice*,
> arXiv:2203.04760 (2022),

which resolves an open question of Filmus–Ihringer (*Boolean constant degree
functions on the slice are juntas*, Discrete Math. 2019). I fetched both papers;
the `k ≥ 2d` threshold and the explicit witness family live only in the 2022
paper, so I formalized against that.

## What I stated

Both directions, plus the explicit witnessing family.

1. `filmus_junta_threshold` — the full biconditional Theorem 1.1:
   - forward: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`, every Boolean degree-`d`
     function on the slice is an `m`-junta;
   - converse: `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`, `∀ m, ∃ n ≥ 2k` and a Boolean
     degree-`d` function on the slice that is not an `m`-junta.

2. `filmus_junta_threshold_witness` — the concrete family
   `Σ_{i<ℓ} Π_{j<e} X_{i·e+j}` with `e = min d k`, asserting it is Boolean,
   degree `≤ d`, and not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

| Choice | Decision | Why |
| --- | --- | --- |
| slice | `{S : Finset (Fin n) // S.card = k}` | direct, matches "sets of size `k`"; `S.1 ∩ J` gives the junta condition cleanly |
| codomain | `Slice n k → ℝ`, Boolean-ness a separate predicate `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1` | the paper works with real-valued functions ({0,1} ⊆ ℝ) and junta test functions `g : {0,1}^J → ℝ`; keeps "degree" over ℝ natural |
| degree ≤ d | `∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ ∀ S, f S = eval (indicator S) p` | exactly the paper's "minimum degree of a (not necessarily multilinear/harmonic) real polynomial agreeing with `f` on all slice points" |
| point of the cube | `indicator S : Fin n → ℝ`, `i ↦ if i ∈ S then 1 else 0` | slice points = indicator vectors of `k`-sets |
| `m`-junta | `∃ J, J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` | equivalent to the paper's `f x = g(x|_J)`; `S ∩ J = T ∩ J` is `x|_J = y|_J` for indicator vectors |
| `m(d)` | existential `∃ m : ℕ` after `d` is fixed | "there is a constant `m(d)`"; a function `ℕ → ℕ` would be equivalent and was the other option |
| `n, k, d` | plain `ℕ`, universally quantified, ambient coordinate set `Fin n` | no reason to bundle |
| witness indexing | block `i : Fin ℓ`, offset `j : Fin (min d k)`, coordinate `finProdFinEquiv (i,j) : Fin (ℓ·e)` then `Fin.castLE h` into `Fin n` | gives contiguous disjoint blocks `{i·e, …, i·e+e−1}` |

## Deviations / corrections from the task prompt

- The prompt renders the witness family as a **product of sums**
  `∏_{i}(Σ_j x_{(i-1)e+j})`. That is a garbling: such a product is neither
  Boolean-valued nor degree `≤ d` on the slice. The actual paper (Thm 1.1 and
  its proof, e.g. `f(x) = a + (b−a) Σ_{i} x_{{(i-1)k+1,…,ik}}`) uses a **sum of
  products** `Σ_{i}∏_j x_{(i-1)e+j}`, degree `e = min(d,k) ≤ d`, and on a slice
  with `k < 2d` at most one monomial fires, so it is `{0,1}`-valued. I
  formalized the sum-of-products version.
- The paper's own subscript `x_{(e-1)i+j}` in the Thm 1.1 blurb produces
  *overlapping* blocks and is almost certainly a typo; the detailed proof uses
  disjoint contiguous blocks `(i-1)e+j`, which is what I used.
- "not `ℓe`-juntas" (paper blurb): the precise bound from the paper's Lemma 2.2
  with `|I| = |J| = ℓe` is "not an `(ℓe−1)`-junta". I stated the robust,
  off-by-one-free form `∀ m < ℓ·e, ¬ IsJunta m f`, which is what feeds the
  `∀ m ∃ …` converse.

## Uncertainties / guessed Mathlib identifiers

- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — name and direction believed
  correct; the exact enumeration order (`i·e+j` vs `j·ℓ+i`) is **not
  load-bearing** for the statement (any injective block layout works).
- `Fin.castLE : (h : n ≤ m) → Fin n → Fin m` — believed correct.
- `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.X` — standard;
  `eval` used as `MvPolynomial.eval v p`.
- `witnessPoly` is marked `noncomputable` defensively (real coefficients).
- `import Mathlib` used for self-containment.
- I kept both `hn : 2*(ℓ*min d k) ≤ n` and the weaker `hle : ℓ*min d k ≤ n`
  (needed to typecheck `witnessPoly`) as separate hypotheses rather than
  deriving one from the other inside the statement.
