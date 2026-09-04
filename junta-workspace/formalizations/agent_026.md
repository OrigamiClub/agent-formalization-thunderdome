# Agent 026 — formalization note

## What I stated

All three pieces, as separate `theorem … := by sorry`:

1. **`filmus_ihringer_forward`** — the upper bound: `∃ M : ℕ → ℕ` such that for all `d ≥ 1`,
   all `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
   `M d`-junta.
2. **`filmus_ihringer_converse`** — the lower bound: for `d ≥ 1`, `1 ≤ k < 2d`, and every `m`,
   there exist `n ≥ 2k` and a Boolean degree-`d` function on the slice that is not an
   `m`-junta.
3. **`filmus_ihringer_witness`** — the explicit family
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, asserting it is Boolean, has
   degree `≤ d` on the slice, and is not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`
  is the most direct rendering of `{S ⊆ [n] : |S| = k}` and makes "`S ∩ J`" literally
  `Finset.inter`.
- **Codomain**: `ℝ` with a separate `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`
  (the `{0,1} ⊆ ℝ` choice). This meshes with the polynomial-agreement definition of degree,
  which is inherently real-valued.
- **Degree `≤ d`** (`BooleanDegreeLE`): existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), and
  `f S = MvPolynomial.eval (indicator S.1) p` for every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. Multilinearity is included because the informal
  statement says "multilinear"; it is WLOG on the slice (`x_i^2 = x_i`). I did **not** add a
  redundant `∑ xᵢ = k` slice relation; the quantifier over slice points already restricts
  agreement to the slice, which is the standard "degree on the slice" notion.
- **`m`-junta** (`IsJunta`): `∃ J, J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **`m(d)`**: existential `∃ M : ℕ → ℕ` at the head of the forward statement, with `d`
  universally quantified inside — reads as "there is a function `d ↦ m(d)`".
- **Carrying `n, k, d`**: plain `ℕ` universally quantified with hypotheses `1 ≤ d`,
  `2*d ≤ k` / `1 ≤ k`, `k < 2*d`, `2*k ≤ n`. Ambient coordinate set is `Fin n`.
- **Explicit family** (`witnessFun n k e ℓ`): `∏_{i ∈ range ℓ} |S ∩ Bᵢ|` with block
  `Bᵢ = {c : (c:ℕ)/e = i}` = coordinates `i·e … i·e+e-1`. The block sum
  `∑_{j} x_{(i-1)e+j}` is rendered as `(S.filter (·/e = i)).card`. Indexing is 0-based over
  `range ℓ`; `e = min d k` is passed as `min d k` at the call site. Room hypothesis
  `2*(ℓ * min d k) ≤ n` matches the informal `n ≥ 2ℓe`.

## Uncertainties / caveats

- **"not `ℓe`-juntas"**: taken literally this is false — `witnessFun` is a function of the
  `ℓe` coordinates `0 … ℓe-1`, hence trivially an `ℓe`-junta. I read the informal phrase as
  "junta number is exactly `ℓe`" and stated `∀ m < ℓ·e, ¬ IsJunta m …` (i.e. not an
  `(ℓe−1)`-junta), which is the unbounded-as-`ℓ→∞` content the converse needs.
- Mathlib identifiers used: `MvPolynomial`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `p.support` (as `Finset (Fin n →₀ ℕ)`), `Finset.filter`, `Finset.card`, `Finset.range`,
  `∏ … ∈ …`. These are standard; I have not run a compiler. `import Mathlib` is used for
  safety.
- Booleanness and degree-`≤ d`-on-the-slice of `witnessFun` are asserted per Filmus–Ihringer,
  not checked here. The degree claim is the non-obvious one (naive polynomial degree is `ℓ`;
  it collapses to `≤ d` using the slice relation), and is captured by the existential in
  `BooleanDegreeLE`.
- Slice non-emptiness: guaranteed by `k ≤ n` (from `2k ≤ n`), so `¬ IsJunta` is not
  vacuously contradicted.
