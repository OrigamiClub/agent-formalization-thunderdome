# agent_092 — formalization note

## What I stated

Three `sorry`-terminated declarations, no proofs:

1. `filmus_ihringer` — **both directions** as a single conjunction:
   - forward: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f, Boolean → degree ≤ d → M-junta`;
   - converse: `∀ d ≥ 1, ∀ k, 1 ≤ k < 2d, ∀ m, ∃ n ≥ 2k, ∃ f, Boolean ∧ degree ≤ d ∧ ¬ m-junta`.
2. `witnessPoly` / `witnessFun` — the **explicit witnessing family**
   `∏_{i=0}^{ℓ-1} (∑_{j=0}^{e-1} X_{i·e+j})` with `e = min d k`, evaluated at the indicator.
3. `witness_spec` — the converse direction realized by `witnessFun`: for every `m` there are
   `ℓ, n` with `m < ℓ·e` and `n ≥ 2k`, `n ≥ 2·ℓ·e`, making `witnessFun` a Boolean degree-`d`
   non-`m`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Chosen because the
  junta condition is naturally phrased with `S.val ∩ J` on `Finset`, and the indicator
  vector `Fin n → ℝ` is immediate. `abbrev` keeps `.val`/`.property` reducible.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` plus `IsBooleanValued f`
  (`∀ S, f S = 0 ∨ f S = 1`). Real codomain is the honest one for "agrees with a real
  polynomial"; `Bool`/`Fin 2` would force casts inside the degree definition.
- **Degree ≤ d**: `HasSliceDegreeLE` = existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (`∀ m ∈ p.support, ∀ i, m i ≤ 1`), and
  `f S = MvPolynomial.eval (indicator S) p` for all slice points. The multilinear clause is
  included to match the problem's wording; on `{0,1}` inputs it does not change the notion
  (reduce `x_i^2 → x_i`), so dropping it would give an equivalent statement.
- **m-junta**: `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.val ∩ J = T.val ∩ J → f S = f T`.
- **m(d)**: existential `∃ M : ℕ` inside the forward statement (not a supplied `m : ℕ → ℕ`).
- **n, k, d**: plain `ℕ` arguments; ambient coordinate set is `Fin n`. Slice non-emptiness is
  not asserted separately but follows from `2*k ≤ n` where that hypothesis appears.
- **Explicit family indexing**: `i ∈ range ℓ`, `j ∈ range e`, coordinate `i*e + j`, guarded
  by `dite (i*e+j < n)`. `ℓ` is kept as a free parameter exactly as in `∏_{i=1}^{ℓ}`.

## Uncertainties

- Guessed / assumed Mathlib identifiers: `MvPolynomial`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X`, `MvPolynomial.support`, `Finset.card`,
  `Finset.range`, big-operator `∏/∑ ... ∈ ...` notation, `Finsupp` application `m i`.
  These are standard but I could not run a compiler.
- I did **not** find a Mathlib native notion of "Boolean degree on the slice" / Johnson
  scheme levels, so I built the polynomial-evaluation definition by hand.
- The exact side conditions on `ℓ` (relative to `d, k`) under which the literal family
  `∏ ∑ x` is genuinely `{0,1}`-valued and of slice-degree `≤ d` are not spelled out in the
  source snippet, and I did not verify them. `witness_spec` transcribes the paper's claim
  ("for `n ≥ 2ℓe`, not an `ℓe`-junta") with `1 ≤ ℓ` added; treat the family part as the
  paper's assertion rather than an independently checked statement. The robust content is
  `filmus_ihringer`, whose converse is a plain existence claim.
- `witnessPoly`/`witnessFun` marked `noncomputable` defensively (MvPolynomial instances).
