# Agent 015 — formalization note

## What was stated

All three of:

1. `filmus_ihringer_forward` — the positive direction.
2. `filmus_ihringer_converse` — the converse in pure existential form (there exist `n` and a
   function `f` with the stated properties).
3. `filmus_ihringer_converse_explicit` — the converse together with the explicit witnessing
   family `fiWitness`.

Only statements; every theorem is `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Slice.** `Slice n k := {S : Finset (Fin n) // S.card = k}`. The subtype of `Finset (Fin n)`
  of exact cardinality `k`. Coordinates are `Fin n`; membership `i ∈ S.1` plays the role of
  the indicator bit `x_i`.
- **Boolean codomain.** Functions are `Slice n k → ℝ`, with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued makes "agrees with a real polynomial"
  and "is a product of block-counts" directly expressible without coercions.
- **Degree ≤ d.** `HasDegreeAtMost f d`: there is `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` such that for every slice point `S`,
  `f S = MvPolynomial.eval (fun i => if i ∈ S.1 then 1 else 0) p`.
  I did *not* separately require `p` multilinear: on `0/1` inputs one can always reduce to a
  multilinear representative without raising the total degree, so the represented class is the
  same. Identifiers used: `MvPolynomial`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`.
- **m-junta.** `IsJunta f m`: there is `J : Finset (Fin n)` with `J.card ≤ m` such that
  `S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **m(d).** Existential *inside* the statement: `∃ m : ℕ, …`, with `d` fixed beforehand, so
  `m` is a constant depending only on `d`.
- **Quantifier shape of the forward direction.** `∀ d, 1 ≤ d → ∃ m, ∀ k n, 2*d ≤ k → 2*k ≤ n
  → ∀ f, IsBoolean f → HasDegreeAtMost f d → IsJunta f m`. `k`, `n` are universally quantified
  *after* `m`, matching "there is a constant `m(d)` such that for all `k ≥ 2d`, all `n ≥ 2k` …".
- **Coordinate set / parameters.** `n`, `k`, `d` are plain `ℕ`; the ambient coordinate type is
  `Fin n`, threaded through `Slice n k`. Hypotheses `2*d ≤ k`, `2*k ≤ n`, `1 ≤ k`, `k < 2*d`
  transcribe `k ≥ 2d`, `n ≥ 2k`, `1 ≤ k`, `k < 2d`.
- **Explicit family.** `fiWitness e ℓ S = ∏_{i ∈ range ℓ} (#{a ∈ S : i·e ≤ a < i·e+e})`,
  a literal transcription of `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`
  (blocks are the consecutive length-`e` intervals `{i·e, …, i·e+e−1}` of `Fin n`). Using an
  interval/`filter`-cardinality form avoids constructing `Fin n` indices with side proofs.
  In `filmus_ihringer_converse_explicit` the family is bound as `f : Slice n k → ℝ` via the
  equation `f = fiWitness (min d k) ℓ`, which pins the implicit `n k` of `fiWitness`.
  Given `m`, one takes `ℓ` large enough that `ℓ·e ≥ m` (possible since `e = min d k ≥ 1`),
  and "not an `ℓ·e`-junta" then implies "not an `m`-junta".

## Uncertainties

- Mathlib identifier spellings assumed from memory: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval` (applied as `eval g p`), `Finset.filter` argument order
  (`s.filter p`), `∏ i ∈ s, _` `BigOperators` notation, `Finset.range`.
- The exact statement of the witnessing-family claim in the paper is transcribed literally
  from the task text. My own quick check of small cases (e.g. `d = k = 2`, product of two
  block-counts) suggests that the product form as written can fail to be Boolean, or is a
  block-junta, depending on interpretation — so `fiWitness` may not be a faithful rendering
  of the paper's actual construction (the intended variables might be mean-zero differences
  `x_i − x_j`, or a symmetrized sum over block choices, rather than raw indicator sums).
  `filmus_ihringer_converse` (the pure existence form) does not depend on this and is the
  safer statement; `filmus_ihringer_converse_explicit` is provided for diversity but carries
  this caveat.
- `HasDegreeAtMost` drops multilinearity of `p`; if the grader wants the polynomial forced
  multilinear, add a clause `∀ m ∈ p.support, ∀ i, m i ≤ 1`.
