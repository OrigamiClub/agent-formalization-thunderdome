# agent_030 — formalization note

## What was stated

Three `sorry`-terminated theorems, no proofs:

1. `boolean_degree_junta_forward` — the forward direction. For `d ≥ 1`,
   `∃ m : ℕ`, for all `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the
   slice is an `m`-junta.  `m(d)` is an **existential inside the statement** (`∃ m`),
   not an explicit `m : ℕ → ℕ`.

2. `boolean_degree_junta_converse` — the converse in **pure existential form**. For
   `1 ≤ k < 2d` and every `m`, there exist `n ≥ 2k` and a Boolean degree-`d` function on
   the slice that is not an `m`-junta.

3. `boolean_degree_junta_converse_witness` — the converse with the **explicit family**
   `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`.  Given `ℓ ≥ 1`, `n ≥ 2ℓe`,
   and `ℓ` pairwise-disjoint size-`e` blocks `B 0, …, B (ℓ-1) ⊆ Fin n`, the induced slice
   function `blockFun B ℓ` is Boolean, has degree `≤ d`, and is not an `m`-junta for any
   `m < ℓe`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`.  `abbrev` (not
  `def`) so subtype coercions and implicit-argument inference see through it.  Coordinates
  carried as `Fin n`; `n`, `k`, `d` are explicit `ℕ` arguments; inequalities as
  `2 * d ≤ k`, `2 * k ≤ n`.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBooleanValued f : ∀ S, f S = 0 ∨ f S = 1`.  Chosen over `Bool`/`Fin 2`/`ZMod 2`
  because "degree" is defined through a *real* polynomial, so keeping `f` real-valued
  avoids coercion noise.
- **Degree ≤ d**: `HasDegreeAtMost f d` := `∃ p : MvPolynomial (Fin n) ℝ`,
  `MvPolynomial.totalDegree p ≤ d` and `∀ S, f S = MvPolynomial.eval (indicator S) p`,
  where `indicator S i = if i ∈ S.1 then 1 else 0`.  Multilinearity is *not* imposed:
  on `0/1` inputs one can multilinearize without raising total degree, so this is the
  standard "degree on the slice".
- **m-junta**: `IsJunta f m` := `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **Explicit family**: `blockPoly B ℓ := ∏ i ∈ range ℓ, ∑ v ∈ B i, MvPolynomial.X v`,
  and `blockFun B ℓ S := MvPolynomial.eval (indicator S) (blockPoly B ℓ)`.  The `ℓ`
  consecutive index blocks `{(i-1)e+1, …, ie}` are abstracted to an arbitrary
  `B : ℕ → Finset (Fin n)` constrained by `hcard` (each of size `e`) and `hdisj`
  (pairwise disjoint) for `i, j < ℓ`.  This avoids `Fin`-bound arithmetic proof
  obligations (`i*e + j < n`) inside a definition while remaining faithful: by the
  `S_n`-symmetry of the slice, the concrete consecutive blocks and any disjoint size-`e`
  blocks give the same conclusion.  `e = min d k` is passed as a hypothesis
  `he : e = min d k`.

## Uncertainties

- Mathlib identifiers used from memory: `MvPolynomial`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval` (as `eval v p`), `MvPolynomial.X`, `Finset.card`, `Disjoint`,
  `Finset.range`.  These are standard; the big-operator notation `∏ i ∈ s, …` /
  `∑ v ∈ s, …` follows current Mathlib (older versions use `in`).
- I could **not** independently verify the literal Boolean-ness / degree-`≤ d` claims for
  the raw product-of-sums polynomial on `binom([n], k)` for all `k` in range (e.g.
  `(x_1+x_2)(x_3+x_4)` naively takes value `2` on some 3-sets).  The statement transcribes
  the paper's asserted family and its asserted properties; the reduction to a genuinely
  low-degree Boolean representative is left inside the `sorry`.
- The paper's phrase "not `ℓe`-juntas" is interpreted as "minimal junta size is `ℓe`,
  hence not an `m`-junta for any `m < ℓe`"; I stated `¬ IsJunta (blockFun B ℓ) m` under
  `hm : m < ℓ * e`.  (Taken fully literally, `blockFun B ℓ` depends only on the `ℓe`
  coordinates in `⋃ B i`, so it *is* trivially an `ℓe`-junta; the non-trivial content is
  the lower bound `m < ℓe`.)
- `m(d)` was left existential; a reviewer wanting an explicit `m : ℕ → ℕ` would move the
  `∃ m` out to a function argument.
