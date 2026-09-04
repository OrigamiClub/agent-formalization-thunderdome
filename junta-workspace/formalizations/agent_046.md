# Agent 046 — formalization note

## What I stated

Both directions of the Filmus–Ihringer theorem, as two separate `theorem … := by sorry`:

- `filmus_ihringer_junta` — the positive direction. `d` and `hd : 1 ≤ d` are
  parameters; `m(d)` is an **existential inside the statement** (`∃ M : ℕ, …`), with
  `k`, `n`, and `f` all quantified under `M`, so `M` depends on `d` alone.
  Shape: `∃ M, ∀ k n, 2d ≤ k → 2k ≤ n → ∀ f, Boolean f → degree f ≤ d → IsJuntaLE f M`.

- `filmus_ihringer_not_junta` — the converse. For fixed `d ≥ 1` and `k` with
  `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a Boolean degree-`d`
  function on the slice that is not an `m`-junta. Stated as a plain existential
  over the witness function.

I also include `FIfamily`, a literal transcription of the displayed witness
polynomial, as a `def` only (no theorem about it).

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; simplest carrier for both "indicator vector" and "`S ∩ J`".
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with
  `IsBooleanFn f : ∀ S, f S = 0 ∨ f S = 1`. Keeping the codomain `ℝ` lets the
  degree condition talk directly about polynomial evaluation without a coercion.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`, with
  `p.totalDegree ≤ d`, `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity), and
  `∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S.1 then 1 else 0`. Multilinearity is WLOG on `0/1`
  inputs but is included to match the prompt's wording ("multilinear").
- **m-junta** (`IsJuntaLE`): `∃ J : Finset (Fin n), J.card ≤ m ∧
  ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **Parameters**: `n k d m` are explicit `ℕ`; ambient coordinate set is `Fin n`.
  `d` is carried as a theorem parameter with `hd : 1 ≤ d` rather than an outer `∀`.
- Inequalities transcribed verbatim from the prompt: positive direction uses
  `2*d ≤ k` and `2*k ≤ n`; converse uses `1 ≤ k`, `k < 2*d`, `2*k ≤ n`.

## Why the explicit family is not in the statement

The prompt's displayed witness is `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )`,
`e = min(d,k)`, claimed to be Boolean, degree `d`, and "not `ℓe`-juntas" for
`n ≥ 2ℓe`. Working over `binom([n],k)` with `k` fixed and `ℓ` growing:

- As literally written (product of block-sums), once `ℓ > k` some block-sum is
  forced to `0`, so the function is identically `0` — a junta, not a witness.
- The natural correction (`∑_i ∏_j`, i.e. "S contains one of `ℓ` disjoint size-`e`
  blocks") is Boolean and degree `≤ d` when `k < 2e`, but it is an `ℓe`-junta:
  take `J` = the `ℓe` block coordinates and the value is determined by `S ∩ J`.
  That contradicts the parenthetical "not `ℓe`-juntas".

I could not reconcile the displayed formula with its stated properties without the
source paper, so rather than commit a `theorem` to a statement I believe is
inconsistent, I encoded the mathematically robust content of the converse — "for
every `m`, some Boolean degree-`d` function on the slice is not an `m`-junta" — and
left `FIfamily` as a reference `def`. The most likely intended reading is that the
family is an `ℓe`-junta that is *not* an `(ℓe−1)`-junta, so letting `ℓ → ∞`
defeats every fixed `m`; that consequence is exactly what `filmus_ihringer_not_junta`
asserts.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf` — name and argument order (`degreeOf (i) (p)`); used the
  explicit `MvPolynomial.degreeOf i p` form to avoid dot-notation mis-resolution.
- `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X` — standard,
  high confidence.
- `∏ i ∈ Finset.range ℓ, …` / `∑ j ∈ Finset.range e, …` big-operator notation
  (older Mathlib used `in`).
- Blanket `import Mathlib`.
- Positive direction's `n ≥ 2k` bound is taken verbatim from the prompt; the
  published theorem may need `n` larger than `2k`.
- Whether "degree-`d`" should be exact degree `= d` vs `≤ d`: used `≤ d`, the
  standard meaning of "Boolean degree `d` function".
