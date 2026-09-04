# Agent 028 — formalization note

## What I stated

Both directions of the theorem, plus the explicit witness, as three `sorry`-terminated theorems
in `namespace FilmusIhringer`:

1. `junta_of_degree_le` — positive direction: `∃ m(d)`, for all `k ≥ 2d`, `n ≥ 2k`, every Boolean
   degree-`d` function on `binom([n],k)` is an `m(d)`-junta.
2. `not_junta_of_degree_le_of_lt` — converse, as a pure existential: for `1 ≤ k < 2d` and every
   `m`, some slice `binom([n],k)` (`n ≥ 2k`) carries a Boolean degree-`d` non-`m`-junta.
3. `blockFun_is_witness` — the explicit family: it is Boolean, has degree `≤ d`, and is not an
   `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Simple, matches the
  set-theoretic `{S ⊆ [n] : |S| = k}`, and `S ∩ J` is just `Finset.inter`.
- **Boolean codomain**: functions `Slice n k → ℝ` with `IsBooleanValued f : ∀ S, f S = 0 ∨ f S = 1`
  (i.e. `{0,1} ⊆ ℝ`). Chosen so that "degree" is stated directly against real polynomials with no
  coercion juggling.
- **Degree ≤ d**: `HasDegreeLE f d := ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
  ∀ S, f S = eval (indicator of S) p`. Uses `MvPolynomial.totalDegree` and `MvPolynomial.eval`
  at the `{0,1}` indicator vector. Multilinearity is *not* imposed: on `{0,1}`-points every
  polynomial agrees with its multilinearization at no greater total degree, so this is equivalent
  to "agrees with a multilinear polynomial of total degree ≤ d".
- **m-junta**: `IsJunta m f := ∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
  Direct reading of "value depends only on `S ∩ J`".
- **m(d)**: existential *inside* the statement (`∃ m : ℕ, ∀ k n …`), matching "there is a constant
  `m(d)`". Not exposed as an `m : ℕ → ℕ`.
- **n, k, d, coordinates**: all explicit `ℕ`; ambient coordinate type `Fin n`. Standing hypothesis
  `2 * k ≤ n` (the paper's `n ≥ 2k`) carried on each statement; positive direction also needs
  `n - k` large, which `2k ≤ n` and `k ≥ 2d` already give.
- **Explicit family**: blocks abstracted as an injective `ι : Fin ℓ → Fin e → Fin n` rather than
  hard-coding the index `(i-1)e + j`, to keep a statement-only file free of `Fin` arithmetic and
  bundled bound proofs. The paper's concrete `ι i j = (i-1)e + j` is one such injective family.
  `ℓ` is the free growth parameter; `e = min d k` is passed as a hypothesis `he : e = min d k`.

## Corrections / uncertainties

- **The witness formula in the task prompt is transposed.** The prompt writes
  `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` (product of sums). The actual construction in
  Filmus, arXiv:2203.04760, is `Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (sum of products) =
  "number of size-`e` blocks entirely contained in `S`". This matters: the product-of-sums is
  *not* `{0,1}`-valued on `binom([n],k)` for these parameters (e.g. `d=2, k=3, e=2, ℓ=2` gives
  value `2`), whereas the sum-of-products is `{0,1}`-valued precisely because `k < 2d ⇒ 2e > k`,
  so at most one disjoint block fits in `S`. I formalized the sum-of-products (`blockPoly`).
- **"not `ℓe`-juntas"**: taken literally the function *is* an `ℓe`-junta (it depends on exactly the
  `ℓe` block coordinates, and `S ∩ (blocks)` determines it). The paper's phrase means "needs all
  `ℓe` coordinates", i.e. not an `(ℓe − 1)`-junta. I stated the equivalent monotone form
  `∀ m, m < ℓ * e → ¬ IsJunta m f`.
- **Attribution**: the prompt says "Filmus–Ihringer". The qualitative "constant-degree ⇒ junta"
  result is Filmus–Ihringer, Discrete Math. 2019. The *sharp* threshold `k ≥ 2d` together with
  this exact witness family is Filmus's solo paper arXiv:2203.04760, Theorem 1.1. Statements here
  follow the latter.
- **Guessed Mathlib identifiers** (all standard, high confidence): `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.X`, `Finset` `∩`/`.card`, `Function.Injective`,
  `∑ / ∏` big operators. I am not aware of any Mathlib notion of "Boolean degree-`d` function on
  the slice" or "junta", so these are defined from scratch.
- I did not attempt proofs; `sorry` closes every theorem. Hypotheses were chosen so the statements
  are (to my analysis) true and provable, not minimal.
