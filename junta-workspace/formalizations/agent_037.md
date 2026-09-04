# agent_037 — Filmus–Ihringer slice juntas: formalization note

## What is stated

Three `sorry`ed theorems, all statement-only:

1. `filmus_ihringer` — **both directions**, for a fixed `d ≥ 1`:
   - positive: `∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f, Boolean f → degree ≤ d → f is an m-junta`;
   - negative: `∀ k, 1 ≤ k < 2d → ∀ m, ∃ n ≥ 2k, ∃ f, Boolean ∧ degree ≤ d ∧ ¬ m-junta`.
2. `filmus_ihringer_witness` — the **explicit family**
   `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, asserting it is Boolean, degree `≤ d`,
   an `ℓe`-junta, and not an `(ℓe−1)`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype chosen so the
  underlying `Finset` and its membership/decidability are available transparently (`abbrev`, not
  `def`, so `↑S`, `.card`, `∩` just work).
- **Boolean codomain**: functions are `Slice n k → ℝ` together with the predicate
  `IsBooleanFn f : ∀ S, f S = 0 ∨ f S = 1`. Using `ℝ` (rather than `Bool`/`Fin 2`) makes the
  degree notion a direct polynomial-agreement statement with no coercion bookkeeping.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with `∀ i, degreeOf i p ≤ 1`
  (multilinear) and `p.totalDegree ≤ d`, such that `f S = eval (sliceIndicator S) p` for every
  slice point. `sliceIndicator S i = if i ∈ S then 1 else 0`. This matches the "agrees on the
  slice with a multilinear real polynomial of total degree ≤ d evaluated at the indicator vector"
  wording. The multilinearity clause is arguably redundant (one can multilinearize) but is kept
  for fidelity.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
  This is the "value depends only on `S ∩ J`" reading. It is monotone in `m`.
- **m(d)**: an existential *inside* the statement (`∃ m : ℕ, …`), with `d` a parameter of the
  theorem. Not packaged as an explicit `m : ℕ → ℕ`; the paper gives no closed form.
- **n, k, d, coordinates**: all `ℕ` parameters; the ambient coordinate set is `Fin n`, carried
  through the polynomial ring `MvPolynomial (Fin n) ℝ`.
- **Explicit family indexing**: 0-based. `blockLinear n e i = ∑_{j∈range e} X_{i*e+j}` (indices
  `≥ n` contribute `0` via `dite`), and `witnessPoly n ℓ e = ∏_{i∈range ℓ} blockLinear n e i`, so
  the variables used are exactly `x_0, …, x_{ℓe−1}`. `witnessFn` is its evaluation at
  `sliceIndicator`.

## Uncertainties / caveats

- **`MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X`**:
  used from memory of Mathlib; signatures believed correct (`degreeOf : σ → MvPolynomial σ R → ℕ`,
  `eval : (σ → R) → MvPolynomial σ R →+* R`).
- **"not ℓe-juntas"**: taken literally the function `∏(∑ x)` depends on exactly the `ℓe`
  coordinates `x_0..x_{ℓe−1}`, hence *is* an `ℓe`-junta. I interpreted the intended claim as
  "its minimal junta support is `ℓe`", i.e. it is an `ℓe`-junta but **not** an `(ℓe−1)`-junta;
  combined with `ℓ → ∞` this yields the negative direction. Stated that way in
  `filmus_ihringer_witness`.
- **Booleanness of the literal witness**: `∏_{i}(∑_{j} x_{ie+j})` evaluated at a `0/1` vector is
  `∏_i |S ∩ B_i|`, which is not obviously `{0,1}`-valued for general `S` on the slice. The task's
  theorem statement asserts these functions *are* Boolean degree-`d`, so `IsBooleanFn` and
  `HasSliceDegreeLE … d` are asserted as part of the (sorried) conclusion; any implicit
  normalization / Booleanization in the source construction is absorbed by the `sorry`. Flagging
  this as the main fidelity risk.
- **Hypotheses on the witness**: both `2*k ≤ n` (slice well-populated) and `2*ℓ*e ≤ n` (the
  "`n ≥ 2ℓe`" condition) are required; `2*ℓ*e` parses as `(2*ℓ)*e`.
- Slice nonemptiness / `Fintype` instances are not needed for the statements and are omitted.
