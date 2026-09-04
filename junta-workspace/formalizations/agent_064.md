# Agent 064 — formalization note

## What is stated

Statement only; every theorem ends `:= by sorry`. I stated **both directions**, and
gave the converse in two forms:

1. `forward_junta` — positive direction. `m(d)` is an **existential inside the
   statement** (`∃ m : ℕ, ...`), matching "there is a constant `m(d)`". The bound is
   uniform over `k ≥ 2d` and `n ≥ 2k`.
2. `converse_exists` — sharpness in plain form: `1 ≤ k < 2d` ⇒ for every `m`, some
   `n ≥ 2k` and some Boolean degree-`d` function that is not an `m`-junta.
3. `converse_witness` — sharpness with the **explicit witnessing family**
   `∏_{i<ℓ} (Σ_{j<e} x_{i·e+j})`, `e = min d k`, indexed with 0-based blocks. It
   asserts the three claimed properties (Boolean, degree `≤ d`, not an `ℓe`-junta)
   for all `ℓ ≥ 1` and all `n` with `n ≥ 2k` and `n ≥ 2ℓe`.

`converse_exists` follows from `converse_witness` by picking `ℓ` with `ℓe ≥ m`
(not being an `ℓe`-junta then implies not being an `m`-junta since `m ≤ ℓe`); I kept
both so the plain form is available without unfolding `witness`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset ℕ // S.card = k ∧ ∀ x ∈ S, x < n}`.
  Coordinates are `ℕ` bounded by `n` rather than `Fin n`. This avoids `Nat.cast`/
  `NeZero n` friction when writing the witness's coordinate `i * e + j`, and keeps the
  block indexing literal.
- **Codomain**: real-valued `f : Slice n k → ℝ` with a separate `IsBoolean`
  predicate (`∀ S, f S = 0 ∨ f S = 1`). Real values are needed to talk about
  polynomial degree; `IsBoolean` pins down `{0,1} ⊆ ℝ`.
- **Degree**: `HasDegreeLE d f := ∃ p : MvPolynomial ℕ ℝ, p.totalDegree ≤ d ∧
  ∀ S, f S = MvPolynomial.eval (ind S) p`, where `ind S i = if i ∈ S.1 then 1 else 0`.
  This is the standard "agrees on the slice with a total-degree-`≤ d` polynomial at
  the 0/1 indicator vector". Multilinearity of `p` is w.l.o.g. (reduce `xᵢ² → xᵢ`;
  does not raise total degree) and is not imposed. Polynomials over all of `ℕ` are
  allowed; variables `≥ n` are always `0` on the slice, so this is harmless.
- **Junta**: `IsJunta m f := ∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J →
  f S = f T` — value determined by `S ∩ J` for a coordinate set of size `≤ m`.
- **Witness**: `witness n k e ℓ S = ∏_{i ∈ range ℓ} ∑_{j ∈ range e} ind S (i*e+j)`.
  `e` is passed explicitly and instantiated to `min d k` in `converse_witness`.
  Added the hypothesis `1 ≤ ℓ` (with `ℓ = 0` the empty product is the constant `1`,
  a `0`-junta) and both `2*k ≤ n` and `2*(ℓ * min d k) ≤ n`.

## Uncertainties / guessed identifiers

- `MvPolynomial.totalDegree` and `MvPolynomial.eval` — names and the fact that `eval`
  takes `(ind S : ℕ → ℝ)` then the polynomial. Fairly confident these are current
  Mathlib.
- `∏ i ∈ Finset.range ℓ, ...` / `∑ j ∈ Finset.range e, ...` big-operator notation with
  `import Mathlib` and `open Finset`. Confident.
- `noncomputable` on `witness` is defensive (ℝ arithmetic); harmless for a
  statement-only file.
- I did not attempt to verify that the explicit family is genuinely Boolean and of
  degree `≤ d` on the slice — the theorem is transcribed as given in the prompt.
- The forward direction's `m(d)` is left fully existential; the paper gives an
  explicit (large) bound, which I chose not to pin down.
