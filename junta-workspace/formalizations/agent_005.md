# agent_005 — formalization note

## What I stated

All three pieces, statement-only, each `:= by sorry`:

1. `boolean_degree_le_junta_of_k_ge_two_d` — the **forward** direction.
   `m(d)` is an existential `∃ m : ℕ` *inside* the statement (not an external
   `m : ℕ → ℕ`), since `d` is already fixed by the theorem binder. Quantifier
   order matches the paper: `m` chosen first, then `∀ k ≥ 2d`, `∀ n ≥ 2k`, `∀ f`.

2. `exists_boolean_degree_le_not_junta_of_k_lt_two_d` — the **converse**, plain
   existential form: for every `m`, some `n ≥ 2k` and some Boolean degree-`d`
   function that is not an `m`-junta.

3. `explicit_witness_not_junta_of_k_lt_two_d` — the **converse with the explicit
   family** `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` so it unfolds transparently. Ambient coordinate set
  is `Fin n`; `n`, `k`, `d` are plain `ℕ` theorem parameters.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain chosen because it makes
  "degree ≤ d" (agreement with a real polynomial) completely direct, and juntas
  only need value equality.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity), and
  `∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S then 1 else 0`. I included the per-variable
  `degreeOf ≤ 1` clause to match the word "multilinear" in the problem; it is
  equivalent to dropping it (multilinearising on `{0,1}^n` never raises total
  degree), so this is a faithful, not a strengthened, hypothesis.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S ∩ J = T ∩ J → f S = f T`. "Depends only on `S ∩ J`."
- **Explicit family**: `witnessPoly emb ℓ e := ∏ i ∈ range ℓ, ∑ j ∈ range e, X (emb (i,j))`.
  Rather than fight `Nat → Fin n` coercions, I pass an abstract placement
  `emb : ℕ × ℕ → Fin n` and *pin it* in the theorem with
  `∀ i j, i < ℓ → j < min d k → (emb (i,j)).val = i * min d k + j`,
  i.e. `emb (i,j)` is exactly coordinate `(i-1)e + j` (0-indexed `i·e + j`). This
  keeps `witnessPoly` total and definitionally clean while still forcing the
  intended polynomial. Blocks are indexed `i ∈ range ℓ`, offsets `j ∈ range e`,
  `e = min d k`.
- **"not ℓe-junta"**: stated as `m < ℓ * min d k ∧ ¬ IsJunta m f`. Taken
  literally, "not an `ℓe`-junta" is false (the set of all `ℓe` used coordinates
  is a valid junta set), so I read the paper's phrasing as "essentially depends
  on all `ℓe` coordinates", i.e. not an `m`-junta for any `m < ℓe`. Choosing `ℓ`
  with `ℓe > m` then yields the plain converse. The `n ≥ 2ℓe` side condition from
  the problem is kept as `2 * (ℓ * min d k) ≤ n`.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf` — fairly sure this exists with signature
  `degreeOf (i : σ) (p : MvPolynomial σ R) : ℕ`; the multilinearity clause could
  instead be phrased via `MvPolynomial.totalDegree` of individual monomials or
  `p.support` support-wise if `degreeOf` is misnamed.
- `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X` — standard,
  high confidence.
- Whether the literal product-of-linear-forms is genuinely `{0,1}`-valued on the
  slice for all `1 ≤ k < 2d` is something I did not verify; here it is only an
  asserted conjunct under `sorry`, so the statement is well-formed regardless.
- `m(d)` as internal `∃ m` vs external function: a defensible alternative is
  `∃ M : ℕ → ℕ, ∀ d ≥ 1, …`; I kept it internal for a tighter statement.
