# Agent 036 — note

## What is stated

All three pieces, none proved (every theorem ends `:= by sorry`):

1. **Forward direction** (`filmus_ihringer`, first conjunct): a single
   `m : ℕ → ℕ`, chosen up front, such that for every `d ≥ 1`, every `k ≥ 2d`, every
   `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `m(d)`-junta.
2. **Converse direction** (`filmus_ihringer`, second conjunct): for every `d ≥ 1` and
   every `k` with `1 ≤ k < 2d`, and for every `m`, there is a slice `binom([n],k)`
   (`n ≥ 2k`) carrying a Boolean degree-`d` function that is not an `m`-junta.
3. **Explicit family** (`familyFun` + `filmus_ihringer_witness`): the product-of-linear-
   forms family, with the properties the problem statement attributes to it.

## Encoding decisions

- **Slice**: `{S : Finset (Fin n) // S.card = k}`. Keeps membership/intersection
  (`S.1 ∩ J`) elementary and avoids `Sym`/`Set` coercions.
- **Ambient coordinates / parameters**: `n k d` are plain `ℕ` binders in each theorem;
  the coordinate set is `Fin n`.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` plus `IsBooleanFun f`
  (`∀ S, f S = 0 ∨ f S = 1`). Chosen so that "degree" can be phrased with a real
  polynomial and the same `f` object appears in both the Boolean and the degree
  hypotheses.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, every monomial multilinear (`MonoMultilinear`: all exponents
  `≤ 1`, stated over `p.support`), and `f S = MvPolynomial.eval (indicator S.1) p`
  for all `S` in the slice. This is the "agrees with a multilinear real polynomial of
  total degree ≤ d at the indicator vector" definition from the problem text.
  Multilinearity is spelled out by hand because I do not know a Mathlib predicate
  `MvPolynomial.IsMultilinear`.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.1 ∩ J = T.1 ∩ J → f S = f T`. Standard "depends only on `S ∩ J`" phrasing.
- **m(d)**: existential `m : ℕ → ℕ` at the head of the forward statement (not an
  explicit function), matching "there is a constant `m(d)`".
- **Family indexing**: `e := min d k`; block `i` is the natural-number interval
  `Ico (i*e) (i*e+e)`; `familyFun n k d ℓ S` is `∏_{i < ℓ} |S ∩ block i|` (as a real
  number). Implemented with `S.1.filter (· ∈ Ico …)` and `.card` to avoid `Fin n`
  bound-proof plumbing. This equals `∏_i (Σ_{j<e} x_{i*e+j})` evaluated at the
  indicator vector. `ℓ` is a free parameter; the witness theorem assumes `n ≥ 2ℓe`,
  and the converse is meant to follow by taking `ℓ` with `ℓ·e > m`.
- Only `n ≥ 2k` is imposed in the forward direction; since `n ≥ 2k` gives
  `n - k ≥ k ≥ 2d`, this already bounds the co-slice side, so no separate
  `k ≤ n - 2d` hypothesis is added.

## Uncertainties

- **Guessed / assumed Mathlib identifiers**: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.support`, `Finset.Ico` on `ℕ`, `Finset.filter`
  with the `s.filter p` argument order. Names/signatures may need adjustment; a
  compiler was not available.
- **No Mathlib "multilinear polynomial" notion** was used; `MonoMultilinear` is my
  ad hoc definition (`∀ i, m i ≤ 1` on each support monomial).
- **Faithfulness of the explicit family** (`filmus_ihringer_witness`): I transcribed
  the family and the three properties (Boolean, degree ≤ d, not `ℓe`-junta for
  `n ≥ 2ℓe`) literally from the problem statement. I have a genuine concern that the
  plain product `∏_i (Σ_{j<e} x_{i*e+j})` is **not** `{0,1}`-valued for all `ℓ` when
  `k ≠ ℓ` (e.g. `d=3, k=2, ℓ=1`: the single block sum takes the value `2` on
  `S = {0,1}`), and that some implicit tie between `ℓ` and `k`, or a different reading
  of the sum, is intended. The `filmus_ihringer` converse conjunct is stated purely
  existentially and does not depend on this family being exactly right; the family
  theorem is included as a best-effort literal rendering and may be false as stated.
- The forward `m(d)` is left fully abstract (existential); no explicit growth rate is
  claimed.
