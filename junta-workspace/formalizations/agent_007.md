# agent_007 — formalization note

## What I stated

All three of:

1. `juntaThreshold_pos` — the positive direction: `∃ m(d)` such that `k ≥ 2d`,
   `n ≥ 2k` force every Boolean degree-`d` function on `binom([n],k)` to be an
   `m(d)`-junta.
2. `juntaThreshold_neg` — the abstract converse: `1 ≤ k < 2d` implies that for
   every `m` there are `n ≥ 2k` and a Boolean degree-`d` non-`m`-junta.
3. `witness_spec` — the explicit witnessing family and its three properties
   (Boolean, degree `≤ d`, not an `m`-junta for `m < ℓ·e`).

Every theorem is `:= by sorry`; nothing is proved.

## Encoding decisions

- **Slice points**: `S : Finset (Fin n)`, with the slice condition carried as the
  hypothesis `S.card = k` wherever needed (rather than a subtype). Keeps the
  polynomial/junta machinery on the familiar `Finset (Fin n)` type. `slice` is
  provided as documentation.
- **Boolean codomain**: functions are `f : Finset (Fin n) → ℝ`, "Boolean" =
  `f S = 0 ∨ f S = 1` on the slice (`BooleanOn`). This is the standard
  analysis-of-Boolean-functions convention and makes "degree" literal.
- **Degree ≤ d** (`DegreeLEOn`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear, and `f S = eval (ind S) p` on the slice,
  where `ind S` is the `{0,1}` indicator vector. Multilinearity is expressed as
  `∀ u ∈ p.support, ∀ i, u i ≤ 1` (every monomial exponent `≤ 1`). Faithful to
  the prompt's "multilinear real polynomial of total degree ≤ d"; on the slice
  dropping multilinearity would give the same function class.
- **m-junta** (`JuntaOn`): `∃ J, J.card ≤ m ∧ (∀ S T on the slice,
  S ∩ J = T ∩ J → f S = f T)`. The "depends only on `S ∩ J`" formulation, which
  is cleaner than exhibiting an explicit `g`.
- **m(d)**: existential inside `juntaThreshold_pos` (`∃ m : ℕ, …`), matching
  "there is a constant `m(d)`".
- **Parameters**: `d, k, n` are explicit; `n` is a section `variable {n : ℕ}`
  picked up by the definitions and by `witness_spec`, while the two main theorems
  bind their own `n`.
- **Explicit family**: `witness e ℓ x S = ∑ i ∈ range ℓ, ∏ j ∈ range e,
  [x i j ∈ S]`, i.e. the number of fully-contained blocks. The block coordinate
  map `x : ℕ → ℕ → Fin n` is an abstract argument pinned by
  `hx : x i j = i * e + j` (as naturals) for `i < ℓ`, `j < e`. This sidesteps
  in-`def` `Fin n` bound proofs while still fixing the intended coordinates
  `(i-1)e + j` (0-indexed here).

## Deliberate corrections to the prompt's wording

- **Sum of products, not product of sums.** The prompt writes the family as
  `∏_{i}(Σ_{j} x_{(i-1)e+j})`. That function is *not* `{0,1}`-valued on the slice
  (a single factor `|S ∩ Bᵢ|` already ranges over `{0,…,e}`). The source
  (arXiv:2203.04760) has `Σ_{i} ∏_{j} x_{(i-1)e+j}` — count of blocks contained
  in `S` — which *is* Boolean exactly when `k < 2d` (a `k`-set cannot contain two
  disjoint `e`-blocks since `k < 2d ≤ 2·min(d,k)`). I formalized the
  sum-of-products version.
- **"not an ℓe-junta" → "not an m-junta for every m < ℓe".** Taken literally the
  witness *is* an `ℓe`-junta: its `ℓe` block coordinates form a valid `J`. The
  real content is that it is not an `(ℓe − 1)`-junta; I stated
  `∀ m, m < ℓ * min d k → ¬ JuntaOn k m (witness …)`. To beat a given `m` one
  picks `ℓ` with `ℓ · min(d,k) > m` (possible since `min(d,k) ≥ 1`), and an
  `n ≥ max (2k) (2ℓe)`.

## Uncertainties / guessed identifiers

- Mathlib names used from memory: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.support`, `Finsupp` application `u i` for
  `u : Fin n →₀ ℕ`, `Finset.range`, and the `∑ i ∈ s, …` / `∏ j ∈ s, …`
  big-operator notation. All standard; exact spelling of `totalDegree` and the
  `eval` application form are the likeliest to need a tweak.
- `import Mathlib` (whole library) for safety; a minimal import set would be
  `Mathlib.RingTheory.MvPolynomial.Basic` +
  `Mathlib.Algebra.BigOperators.Basic` + `Mathlib.Data.Real.Basic`.
- No attempt was made to check that the `sorry`ed statements are provable as
  written — this is a statement-only deliverable. In particular the "degree ≤ d"
  witness polynomial for `witness_spec` is `∑ i ∈ range ℓ, ∏ j ∈ range e,
  X (x i j)`, whose `totalDegree` is `min d k ≤ d`.
