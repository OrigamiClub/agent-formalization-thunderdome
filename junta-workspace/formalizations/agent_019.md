# Agent 019 — formalization note

## What is stated

All three of:

1. `filmus_ihringer_junta_pos` — the positive direction. `d ≥ 1`, and there
   *exists* `M : ℕ` (the constant `m(d)`, quantified inside the statement, chosen
   before `k`, `n`, `f`, so independent of them) such that for `k ≥ 2d` and
   `n ≥ 2k`, every Boolean degree-`≤ d` function on the slice is an `M`-junta.
2. `filmus_ihringer_junta_neg` — the converse, with an abstract witness: for
   `1 ≤ k < 2d` and every `m`, there exist `n ≥ 2k` and a Boolean degree-`≤ d`
   function on the slice that is not an `m`-junta.
3. `filmus_ihringer_junta_neg_explicit` — the converse with the explicit
   witnessing family `hardFun` from the problem statement.

Statement only; every theorem ends `:= by sorry`, no proofs.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. `Fin n` stands in
  for `{1,…,n}`. Subtype of `Finset` keeps membership/intersection cheap.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain chosen so that the
  degree condition (polynomial evaluation) is stated without any coercion.
- **Degree ≤ d**: `HasDegreeLE d f` = there is `p : MvPolynomial (Fin n) ℝ` that
  is multilinear (`IsMultilinear`: every exponent in every support monomial is
  `≤ 1`) with `p.totalDegree ≤ d`, agreeing with `f` at every slice point via
  `MvPolynomial.eval (indicator S) p`, where `indicator S i = if i ∈ S then 1
  else 0`. This is the "agrees on the slice with a multilinear real polynomial of
  total degree ≤ d evaluated at the indicator vector" reading. Note the
  polynomial only has to agree *on the slice*, so `hardFun` (whose naive total
  degree is `ℓ`) can still satisfy `HasDegreeLE d` via slice reduction.
- **m-junta**: `IsJunta m f` = there is `J : Finset (Fin n)`, `J.card ≤ m`, with
  `f` constant on slice points sharing the same `S ∩ J`.
- **m(d)**: existential `∃ M : ℕ` inside the positive statement (not an explicit
  `m : ℕ → ℕ`).
- **Parameters**: `n k d` are plain `ℕ` arguments/quantifiers; the ambient
  coordinate type is `Fin n`. Hypotheses `2*d ≤ k`, `k < 2*d`, `2*k ≤ n`.
- **Explicit family** (`hardFun n k d ℓ`): `e := min d k`, `ℓ` = number of
  blocks, block `i` (`i : Fin ℓ`) uses coordinates `i*e + j` (`j : Fin e`).
  Out-of-range indices (`i*e+j ≥ n`) contribute `0` via a dependent `if`. The
  explicit theorem quantifies `ℓ` and `n` existentially with `m < ℓ*e` and
  `2*(ℓ*e) ≤ n`, and concludes `hardFun` is not an `(ℓ*e)`-junta (matching "for
  `n ≥ 2ℓe` are not `ℓe`-juntas"), which gives non-`m`-junta since `m < ℓ*e`.

## Uncertainties

- `IsMultilinear` is a hand-rolled predicate (no single canonical Mathlib name I
  was confident of). On `0/1` inputs multilinear vs. arbitrary polynomial does
  not change representable functions, but I included it to match the wording
  "multilinear real polynomial".
- Guessed Mathlib identifiers: `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `MvPolynomial.support`, `Finsupp` application `m i`, `Finset.prod`/`Finset.sum`
  `∏`/`∑` notation. Names/signatures believed current but not compiler-checked.
- Fidelity caveat on `hardFun`: the problem statement asserts these product
  functions are Boolean and degree-`d` on the slice. I transcribed the algebraic
  form verbatim and stated `IsBoolean`/`HasDegreeLE` as *conclusions* of the
  explicit theorem rather than making them definitionally true; I did not verify
  that the literal product `∏_i (∑_j x_{i e+j})` is `{0,1}`-valued on every
  `k`-slice for all admissible parameters. The abstract converse
  (`filmus_ihringer_junta_neg`) is independent of this and is the safe form.
- `Slice n k` can be empty (e.g. `k > n`); the hypotheses `n ≥ 2k` (and `k ≥ 1`)
  keep it nonempty in the regimes that matter, but no nonemptiness is asserted
  explicitly.
