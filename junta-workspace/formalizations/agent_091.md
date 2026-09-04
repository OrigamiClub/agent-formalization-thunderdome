# Agent 091 — formalization note

## What is stated

Three `:= by sorry` theorems, all statement-only:

1. `filmus_ihringer_forward` — the forward direction. `m(d)` is an **existential** `∃ m : ℕ`
   inside the statement (not an explicit `m : ℕ → ℕ`), which matches "there is a constant
   `m(d)`".
2. `filmus_ihringer_converse` — the converse/tightness direction in a clean existential form:
   for `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a Boolean degree-`d` slice
   function that is not an `m`-junta.
3. `filmus_ihringer_converse_witness` — the converse together with the **explicit witnessing
   family** `∏_{i}( ∑_j x_{ie+j} )` with `e = min d k`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. `abbrev` (reducible) so
  that `S.1 : Finset (Fin n)` and `.card` projections work transparently. Ambient coordinate
  set is `Fin n`; `n`, `k`, `d` are plain `ℕ` arguments carried explicitly per theorem.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a separate predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2` because the
  degree notion needs a real polynomial and evaluation into `ℝ`; keeping the codomain `ℝ`
  avoids coercions in `HasDegreeLE`.
- **Degree ≤ d** (`HasDegreeLE`): there exists `p : MvPolynomial (Fin n) ℝ` that is
  multilinear, has `p.totalDegree ≤ d`, and satisfies
  `f S = MvPolynomial.eval (indicator S.1) p` for every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. Multilinearity is spelled out as
  `IsMultilinear p := ∀ m ∈ p.support, ∀ i, m i ≤ 1` (I did not find a Mathlib predicate for
  "multilinear multivariate polynomial"). It is included to be faithful to the problem's
  "Terms" paragraph; on the `0/1` cube it does not change the represented function class.
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J →
  f S = f T`. This is the "value depends only on `S ∩ J`" formulation.
- **Explicit family** (`blockProdPoly ℓ e n`): `∏_{i ∈ range ℓ} ∑_{j ∈ range e} X_{i*e+j}`,
  0-indexed, with a dependent `if` sending out-of-range indices to `0` (they never fire when
  `ℓ*e ≤ n`). Indexing: block `i`, offset `j`, coordinate `i*e + j : Fin n`. The witness
  theorem takes `ℓ` and `n` as parameters with `n ≥ 2*ℓ*e` and `n ≥ 2k`, asserts `f` is the
  induced slice function, and that it is Boolean, degree `≤ d`, and not an `m`-junta for any
  `m < ℓ*e`.

## Uncertainties

- **Guessed / assumed Mathlib identifiers**: `MvPolynomial.totalDegree`, `MvPolynomial.eval`
  (used applicatively as `MvPolynomial.eval v p`), `MvPolynomial.X`, `MvPolynomial.support`,
  `Finset.card`, `Finset.range`, big-operator notation `∏ i ∈ s, _` / `∑ j ∈ s, _`. These are
  standard and I am fairly confident, but I have no compiler here.
- Mathlib has, to my knowledge, **no** built-in notion of "the slice", "Boolean degree", or
  "junta", so all four are custom defs.
- **"not ℓe-juntas"**: taken literally, a function depending on exactly `ℓe` coordinates *is*
  an `ℓe`-junta. I read the intended content as "needs all `ℓe` coordinates", i.e. not an
  `m`-junta for any `m < ℓ*e`, and stated it that way (this is exactly what feeds the
  converse: pick `ℓ` with `ℓ*e > m`).
- **Boolean-ness of the raw product family**: I could not convince myself that the plain
  product `∏_i (∑_j x_{ie+j})` evaluates to `{0,1}` on every `k`-set for all admissible
  parameters (e.g. `k=3, e=2, ℓ=2`, `S = {0,1,2}` gives `(1+1)(1+0) = 2`). The problem text
  asserts the witnesses are Boolean degree-`d`; I formalized the statement as given, but flag
  that the paraphrase may omit a Boolean-ization / a parameter restriction from the
  Filmus–Ihringer construction. The `HasDegreeLE` conclusion for this family is an existential
  over *some* degree-`≤ d` representation (not `blockProdPoly` itself, whose total degree is
  `ℓ`), relying on slice relations to lower the degree to `≤ e = min d k`.
