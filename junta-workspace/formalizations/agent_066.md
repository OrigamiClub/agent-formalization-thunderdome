# Agent 066 — Filmus–Ihringer junta theorem, statement formalization

## What I stated

Three theorems, all `:= by sorry`, no proofs:

1. `filmus_ihringer_forward` — the positive direction. `∃ M : ℕ`, for all `k ≥ 2d`,
   all `n ≥ 2k`, every Boolean, slice-degree-`≤ d` function on `binom([n],k)` is an
   `M`-junta. `m(d)` is an existential inside the statement (matches "there is a
   constant m(d)").
2. `filmus_ihringer_converse` — the converse in clean existential form: for
   `1 ≤ k < 2d` and every `m`, there exist `n ≥ 2k` and a Boolean, slice-degree-`≤ d`
   function that is not an `m`-junta. This is the mathematically robust core and does
   not depend on the exact witness.
3. `filmus_ihringer_converse_explicit` — the converse instantiated with the explicit
   Filmus–Ihringer product family `fiWitness`. Claims that for every `m` there is a
   family member (`ℓ`, `n` with `ℓ·e ≥ m`, `n ≥ 2·ℓ·e`, `e = min d k`) that is
   Boolean, slice-degree-`≤ d`, and not an `ℓ·e`-junta.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`
  is the most direct rendering of "`k`-subsets of `{1,…,n}`", and `S ∩ J` /
  `i ∈ S` are then literal `Finset` operations.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with a predicate
  `IsBooleanValued f : ∀ x, f x = 0 ∨ f x = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  because "degree" is about a *real* multilinear polynomial, so keeping `f` in `ℝ`
  avoids a coercion in the degree definition.
- **Degree `≤ d`** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, every support monomial squarefree (`∀ t ∈ p.support, ∀ i,
  t i ≤ 1`, encoding "multilinear"), and `f S = MvPolynomial.eval (indicator of S) p`
  for all `S` in the slice. Agreement is required only on the slice, which is the
  standard definition of degree on the slice (the representative is not unique
  because of `Σ xᵢ = k`). I kept the explicit multilinearity clause to match the
  problem's "multilinear real polynomial"; it does not change the `≤ d` notion.
- **`m`-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S ∩ J = T ∩ J → f S = f T`. Direct rendering of "value depends only on
  `S ∩ J`".
- **Parameters**: `n, k, d, m, ℓ` all `ℕ`, carried explicitly; the ambient
  coordinate set is `Fin n`, threaded through every definition.
- **Explicit family** (`fiWitness n d k ℓ`): `∏_{i<ℓ} ( Σ_{x ∈ S} [x ∈ Bᵢ] )` where
  block `Bᵢ = {a : i·e ≤ a < i·e + e}`, `e = min d k`. Indexing is 0-based
  (`i ∈ range ℓ`, block `i` covers `[i·e, i·e+e)`), the natural translation of the
  1-based `∏_{i=1}^{ℓ} Σ_{j=1}^{e} x_{(i-1)e+j}`. Written as a sum of `0/1`
  indicators over `x ∈ S`, so the `i`-th factor is exactly `|S ∩ Bᵢ|` and no
  `Fin n` index arithmetic / bounds proof is needed (works for every `n`).

## Uncertainties

- **Mathlib identifiers used** (from memory, not compiler-checked):
  `MvPolynomial (Fin n) ℝ`, `MvPolynomial.totalDegree`, `MvPolynomial.support`
  (`Finset (Fin n →₀ ℕ)`), `MvPolynomial.eval`, and `Finsupp` coercion `t i`. I am
  fairly confident these exist with these names; `p.support` vs a namespaced
  `MvPolynomial.support` and the exact `eval` argument order are the likeliest
  spots to need adjustment.
- **The explicit family (`filmus_ihringer_converse_explicit`)**: I transcribed the
  witness literally as `∏_{i<ℓ} |S ∩ Bᵢ|` per the problem text. I could not verify
  from memory that this literal product is `{0,1}`-valued on `binom([n],k)` for all
  `k` in range (a naive reading gives factors `> 1`, or the whole product `≡ 0` when
  `ℓ > k`). The intended object is very likely this polynomial *reduced modulo the
  slice relations* `Σ xᵢ = k`, `xᵢ² = xᵢ` (which collapses its degree to `≤ d` and
  can make it Boolean), or an indicator variant with the same support. If the
  literal product is not Boolean, `filmus_ihringer_converse_explicit` as written
  would be unprovable; `filmus_ihringer_converse` (theorem 2) is the safe statement
  of the converse and does not rely on the witness form.
- I did not restate `d ≥ 1` as a hypothesis of the converse theorems beyond keeping
  `hd`; it is anyway implied by `1 ≤ k < 2d`.
