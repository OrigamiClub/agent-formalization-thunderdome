# Agent 002 — formalization note

## What I stated

All three parts, as one conjunction inside `theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d)`:

1. **Positive direction.** `∃ m : ℕ, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f`, if `f` is Boolean and has
   degree `≤ d` on `binom([n],k)` then `f` is an `m`-junta. Since `d` is fixed in the
   context, the inner `∃ m` is exactly the promised constant `m(d)`.
2. **Negative direction.** `∀ k` with `1 ≤ k < 2d`, `∀ m`, `∃ n ≥ 2k` and a Boolean
   degree-`≤ d` function on `binom([n],k)` that is not an `m`-junta.
3. **Explicit family.** `∀ k` with `1 ≤ k < 2d`, `∀ ℓ n` with `n ≥ 2·ℓ·min d k` and
   `n ≥ 2k`, the function `juntaWitness d ℓ hn` is Boolean, has degree `≤ d`, and is not an
   `m`-junta for any `m < ℓ·min d k`. Part 3 is a concrete strengthening of part 2
   (take `ℓ` with `ℓ·min d k > m`).

## Encoding decisions

- **Slice:** `Slice n k := { S : Finset (Fin n) // S.card = k }`. `Fin n` stands in for
  `{1,…,n}`. Chose the subtype so that "`|S| = k`" is carried by the type and quantifiers
  range exactly over the slice.
- **Boolean codomain:** real-valued `f : Slice n k → ℝ` together with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain (rather than `Bool`/`Fin 2`) makes
  the degree definition via a real polynomial completely direct with no coercion layer.
- **Degree `≤ d`:** `HasDegreeLE d f` = there exists `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` such that `f S = MvPolynomial.eval (indicator of S) p` for every slice
  point. I did **not** require `p` multilinear: on the slice/hypercube this yields the same
  class of degree-`≤ d` functions, and dropping it keeps the statement shorter.
- **`m`-junta:** `IsJunta m f` = `∃ J : Finset (Fin n)`, `J.card ≤ m` and
  `∀ S T, S ∩ J = T ∩ J → f S = f T`. Direct transcription of "value depends only on
  `S ∩ J`".
- **`m(d)`:** existential *inside* the statement (`∃ m : ℕ, …`), not an external
  `m : ℕ → ℕ`. The theorem asserts existence of the constant, which is what the source
  states; an explicit function would be a stronger, unstated claim.
- **`n`, `k`, `d`, coordinates:** plain `ℕ`s, universally quantified with hypotheses
  (`2*d ≤ k`, `2*k ≤ n`, etc.); ambient coordinate set is `Fin n`.
- **Explicit family indexing:** `blockCoord hn i j : Fin n` is coordinate `i·e + j` for
  `i : Fin ℓ`, `j : Fin e`, `e = min d k`, under `hn : 2·ℓ·e ≤ n` (which also supplies the
  in-range proof for `Fin n`). `juntaWitness d ℓ hn S` is the cardinality (cast to `ℝ`) of
  `{ i : Fin ℓ | ∀ j, blockCoord hn i j ∈ S }`, i.e. the number of fully-contained blocks —
  the slice restriction of `∑_{i<ℓ} ∏_{j<e} x_{i·e+j}`.

## Interpretation choices / uncertainties

- **"product of sums" vs "sum of products".** The prompt writes the witness as
  `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`. Taken literally over `ℝ` this is
  `∏_i |S ∩ B_i|`, which is **not** `{0,1}`-valued on the slice in general (e.g. `e = 2`,
  `ℓ = 1`, `k = 2`), so it cannot be a Boolean degree-`d` function. The construction that
  *is* Boolean of degree `e ≤ d` on `binom([n],k)` when `k < 2·min(d,k)` is the
  **sum of products** `Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (count of fully-contained
  disjoint `e`-blocks; `k < 2e` forces the count into `{0,1}`). I formalized that. I read
  the prompt's `∏(Σ …)` as a transcription slip for `Σ(∏ …)`.
- **"not `ℓe`-juntas".** A function depending essentially on exactly `ℓe` coordinates *is*
  trivially an `ℓe`-junta but not an `(ℓe−1)`-junta. I therefore stated the mathematically
  robust form: `juntaWitness` is not an `m`-junta for any `m < ℓ·min d k`. This captures
  the intended "beats every `m`" content and matches part 2; I did not try to reproduce a
  possible off-by-one in the phrase "`ℓe`-juntas".
- **Hypotheses on `n` for part 3.** I require `n ≥ 2·ℓ·min d k` (the prompt's `n ≥ 2ℓe`)
  and additionally `n ≥ 2k`. These are chosen to be comfortably sufficient rather than
  minimal; a tighter statement might need less.
- **"degree `d`" = "degree `≤ d`".** Standard in this literature; I used `≤ d` throughout.
- **Guessed Mathlib identifiers** (no compiler was available): `MvPolynomial`,
  `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `Finset.filter` / `Finset.univ` /
  `Finset.card`, `mul_le_mul_right'`, and `open scoped Classical` for the `DecidablePred`
  instance in `juntaWitness`. The `blockCoord` bound is discharged by `omega` after
  supplying `ring` identities and one `mul_le_mul_right'` step (omega abstracts the
  nonlinear products as atoms). These are proof-side and not part of the statement, but a
  name change would need a small fix.
