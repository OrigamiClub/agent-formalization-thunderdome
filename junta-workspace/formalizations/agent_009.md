# Agent 009 — formalization note

## What is stated

A single theorem `FilmusIhringer.junta_threshold (d : ℕ) (hd : 1 ≤ d)` whose
conclusion is the **conjunction of both directions** of the Filmus–Ihringer
junta-threshold theorem:

1. **Positive direction** (`k ≥ 2d`): `∃ m : ℕ`, for all `k ≥ 2d`, all `n ≥ 2k`,
   every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.
2. **Negative direction** (`1 ≤ k < 2d`): for every `m` there exist `n ≥ 2k` and a
   Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.

Statement only: the theorem ends in `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Slice.** `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; ambient coordinate set is `Fin n`. Chosen for directness of
  the "`S ∩ J`" junta condition and of the indicator vector.
- **Boolean codomain.** Functions are `Slice n k → ℝ` together with a predicate
  `IsBooleanValued f : ∀ x, f x = 0 ∨ f x = 1`. Real codomain is chosen so that
  "degree" via real polynomials needs no coercion.
- **Degree `≤ d`.** `DegreeLE n k d f := ∃ p : MvPolynomial (Fin n) ℝ,
  p.totalDegree ≤ d ∧ ∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S then 1 else 0`. Multilinearity of `p` is **not**
  imposed: on `{0,1}` points multilinearization does not raise total degree, so
  the notion is equivalent to "agrees with a multilinear polynomial of total
  degree `≤ d`". Effect on the two directions: this makes the positive direction
  marginally stronger (more `f` in scope) and the negative direction marginally
  weaker (easier to exhibit a representative); both are standard-equivalent.
- **`m`-junta.** `IsJunta n k m f := ∃ J : Finset (Fin n), J.card ≤ m ∧
  ∀ S T, (↑S ∩ J = ↑T ∩ J) → f S = f T`. "Depends only on `S ∩ J`."
- **`m(d)`.** Existential `∃ m : ℕ` at the head of the positive direction. This
  is equivalent to providing an explicit `m : ℕ → ℕ` (specialize/abstract on
  `d`), and keeps the statement self-contained.
- **Parameters.** `d` is a fixed hypothesis variable with `1 ≤ d`. `k` and `n`
  are quantified inside each direction exactly as the prose phrases them. The
  numeric thresholds are transcribed as `2 * d ≤ k`, `k < 2 * d`, `2 * k ≤ n`
  (`n ≥ 2k`).

## Explicit witnessing family: deliberately omitted

The source describes the negative-direction witnesses as
`∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d,k)`, "which for
`n ≥ 2ℓe` are not `ℓe`-juntas". Read literally, this formula does **not** satisfy
the three asserted properties once `ℓ ≥ 2`, so I did not encode it as a theorem:

- `d = 1 ⇒ e = 1`, and `1 ≤ k < 2d` forces `k = 1`. The formula is `x_1·…·x_ℓ`,
  which on `binom([n],1)` is identically `0`: it is Boolean and degree `0 ≤ d`,
  but it is a constant, hence a `0`-junta — so "not an `ℓe`-junta" is false.
- For `d ≥ 2` with `d ≤ k`: `e = d` and `|S∩B_1|·|S∩B_2|` can equal `2`, so the
  raw product of block-sums is not `{0,1}`-valued.
- A product of `ℓ` linear forms such as `x_1x_2x_3` has genuine slice-degree `3`,
  exceeding `d` when `d < 3`, so "degree `d`" also fails for the literal formula.

The mathematically intended phenomenon — the witnesses genuinely depend on
`ℓe → ∞` coordinates, so no fixed `m` works — is exactly what the existential
negative direction expresses, which is what I stated. This is the principal
uncertainty / point of interpretation in this formalization.

## Guessed / assumed Mathlib identifiers

- `MvPolynomial (Fin n) ℝ`, `MvPolynomial.eval`, `MvPolynomial.totalDegree` —
  standard Mathlib; `totalDegree` is `ℕ`-valued with `totalDegree 0 = 0`.
- `Finset.card`, `Finset.inter` (`∩` on `Finset`), subtype coercion `↑S`.
- `import Mathlib` (whole library) is used for safety, so the file is
  self-contained without hunting for minimal imports.
