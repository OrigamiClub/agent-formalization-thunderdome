# Agent 020 — formalization note

## What is stated

All three of the following, statement only (`:= by sorry`):

1. `boolean_degree_le_isJunta` — the **forward direction**: for `d ≥ 1` there is
   `m` (existential, after `d` is fixed) such that for all `k ≥ 2d`, all `n ≥ 2k`,
   every Boolean degree-`d` function on the slice is an `m`-junta.
2. `exists_boolean_degree_le_not_isJunta` — the **converse / sharpness**: for
   `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` carries a Boolean degree-`d`
   function that is not an `m`-junta.
3. `blockFun_not_isJunta` — the **explicit witnessing family**
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{c i j})`, `e = min d k`, asserting Boolean-ness,
   degree `≤ d`, and non-`m`-junta for `ℓ·e > m`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset` is the lightest representation and makes `S ∩ J` (junta condition) and
  the indicator vector immediate. Ambient coordinate set is `Fin n`; `n, k, d`
  are plain `ℕ` arguments/quantifiers.
- **Boolean codomain**: functions are `Slice n k → ℝ` with an explicit clause
  `∀ S, f S = 0 ∨ f S = 1`. Using `ℝ` (rather than `Bool`/`Fin 2`) lets
  "agrees with a real polynomial" be stated as a literal equality with no
  coercion.
- **Degree ≤ d**: `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`,
  multilinear (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), and
  `∀ S, f S = MvPolynomial.eval (indicator S) p` where
  `indicator S i = if i ∈ S.1 then 1 else 0`. Multilinearity is included to match
  the theorem text; it does not change the function class on `{0,1}` points, and I
  spelled it via the support because I did not want to rely on a possibly
  non-existent `MvPolynomial.IsMultilinear`.
- **m-junta**: `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **`m(d)`**: existential inside the statement rather than a global `m : ℕ → ℕ`
  (equivalent; slightly less clutter).
- **Witness family**: parameterized by an injective placement
  `c : Fin ℓ → Fin e → Fin n` instead of hard-coding indices `(i-1)e+j`, so the
  `Fin n` bounds need no in-`def` arithmetic proof; `c i j = (i-1)e+j` recovers
  the displayed formula. `blockPoly` is the arithmetic product of sums of `X`s.

## Uncertainties

- Mathlib identifiers used: `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `MvPolynomial.X`, `MvPolynomial.support`, `Function.Injective`, `Finset.card`,
  `∏/∑` big-operator notation. These are standard; exact namespacing of
  `totalDegree`/`support` (dot-notation `p.totalDegree`, `p.support`) is assumed
  to work.
- **The witness family may be too literal.** Read as arithmetic operations on
  `MvPolynomial`, `blockFun` is a product of block-occupancy *counts* and is not
  `{0,1}`-valued in general (e.g. `d ≥ 2`), and degenerates for `d = 1` (`e = 1`,
  product ≡ 0 for `ℓ ≥ 2`). The paper's construction presumably intends Boolean
  connectives (block-AND of block-ORs) and/or relies on a slice-specific degree
  reduction to bring the apparent degree `ℓe` down to `d`. `BooleanDegreeLE` only
  asks for *some* degree-`≤ d` polynomial agreeing on the slice, which is the
  honest form of that claim — but if the literal `blockFun` is not `{0,1}`-valued
  then theorem 3 as transcribed is vacuous/false. Theorems 1 and 2 are the
  robust content; theorem 3 is included to honor the "explicit family" option and
  should be read with this caveat.
- "Not an `ℓe`-junta" in the source is taken to mean "not an `m`-junta for
  `m < ℓe`" (the function genuinely depends on all `ℓe` placed coordinates);
  encoded as `m < ℓ * min d k → ¬ IsJunta … m`.
