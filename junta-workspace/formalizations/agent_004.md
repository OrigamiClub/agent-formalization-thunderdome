# agent_004 — formalization note

## What is stated

Two theorems, both statement-only (`:= by sorry`):

1. `filmus_ihringer` — **both directions** of the Filmus–Ihringer theorem, as a
   single conjunction, parametrized by `d` with hypothesis `1 ≤ d`:
   - junta side: `∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f, Boolean → degree ≤ d → M-junta`;
   - sharpness side: `∀ k, 1 ≤ k → k < 2d → ∀ m, ∃ n ≥ 2k, ∃ f, Boolean ∧ degree ≤ d ∧ ¬ m-junta`.

2. `filmus_ihringer_explicit_witness` — the **explicit witnessing family**
   `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, stated as: for all
   `ℓ` and all `n ≥ 2ℓe` (and `n ≥ 2k`), `famFn` is Boolean, has degree `≤ d`, and
   is not an `ℓe`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `S.val` is the underlying finset, `S.property` the cardinality
  fact. Chosen for direct access to `∩` with a coordinate set `J`.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain is needed anyway for the
  polynomial-agreement definition of degree, so a `{0,1} ⊆ ℝ` side condition is
  the least-friction choice (no coercions in the degree definition).
- **Degree ≤ d**: `HasDegreeLE f d` := `∃ p : MvPolynomial (Fin n) ℝ`,
  `p.totalDegree ≤ d` and `∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S.val then 1 else 0`. This is the "represented by a real
  polynomial of total degree ≤ d on the slice" definition. Multilinearity is
  **not** required (it is WLOG on `{0,1}` inputs and does not raise total degree);
  noted in the file.
- **m-junta**: `IsJunta f m` := `∃ J : Finset (Fin n)`, `J.card ≤ m`,
  `∀ S T, S.val ∩ J = T.val ∩ J → f S = f T`. Standard "value determined by the
  restriction to `J`" phrasing; `J` as a `Finset` gives `card` directly.
- **m(d)**: an **existential inside the statement** (`∃ M : ℕ, …`), placed after
  `d` is fixed, so it depends only on `d`. Not exposed as an `m : ℕ → ℕ`.
- **n, k, d**: plain `ℕ`; `n` is a genuine type parameter (it indexes `Fin n` and
  hence the whole slice type), quantified inside. Inequalities as `2 * d ≤ k`
  etc.
- **Explicit family indexing**: `ℓ` blocks of size `e`, coordinates given by
  `blockEmb : Fin ℓ × Fin e → Fin n` = `Fin.castLE h ∘ finProdFinEquiv`
  (`h : ℓ * e ≤ n`). `famFn` is the product over `Fin ℓ` of the sum over `Fin e`
  of `indicator S` at those coordinates — mirroring `∏ ∑ x`. `e = min d k` is
  carried as a hypothesis `he : e = min d k` rather than a `let`.

## Uncertainties / guessed identifiers

- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — believed to be in
  `Mathlib.Logic.Equiv.Fin` with this name and orientation; used only to build
  `blockEmb`. If the name/direction is off, replace `blockEmb` by an explicit
  `⟨i * e + j, _⟩` with an arithmetic bound proof.
- `Fin.castLE`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `Finset.card`, `Finset` `∩` — standard, high confidence.
- The `(by omega)` obligations discharge `ℓ * e ≤ n` from `2 * (ℓ * e) ≤ n`
  (treating `ℓ * e` as an atom); expected to work.
- **Faithfulness caveat on the explicit witness.** The task specifies the witness
  literally as `∏ (∑ x_j)`. Taken literally as a real polynomial, `∏ ∑ x` need not
  be `{0,1}`-valued on every `k`-set (a block can receive two elements), so
  `IsBoolean (famFn …)` as transcribed may be stronger than the literal product
  supports; the paper's construction presumably intends a per-block OR, or relies
  on a slice degree/Boolean reduction I did not reconstruct here. The statement is
  transcribed as instructed and left as `sorry`; `HasDegreeLE` only asks for
  *some* degree-`≤ d` polynomial, so it does not clash with the product having
  polynomial degree `ℓ`.
- Only the *statement* is claimed; no proof obligations were checked for
  satisfiability beyond type-level consistency (I have no Lean compiler here).
