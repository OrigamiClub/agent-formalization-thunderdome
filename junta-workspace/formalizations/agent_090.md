# Agent 090 — note

## What I stated

Statement only; every theorem ends `:= by sorry`. I stated **both directions** and
**the explicit witnessing family**, as three separate theorems sharing four
auxiliary definitions:

- `filmus_ihringer_positive` — for `d ≥ 1`, `∃ m`, `∀ k ≥ 2d`, `∀ n ≥ 2k`: every
  Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.
- `filmus_ihringer_converse` — for `1 ≤ k < 2d` and every `m`: `∃ n ≥ 2k` and a
  Boolean degree-`d` function that is **not** an `m`-junta.
- `filmus_ihringer_explicit_family` — same as the converse but exhibiting the
  witness `filmusFamily d k ℓ n` for suitable `ℓ, n`. (This theorem implies
  `filmus_ihringer_converse`; I kept both — the clean existence claim and the
  constructive one.)

## Encoding decisions

| Choice | Decision | Why |
|---|---|---|
| Slice | `f : Finset (Fin n) → ℝ` guarded everywhere by `S.card = k` | Lightest; makes "agrees with a real polynomial" and "`S ∩ J`" completely direct. No subtype/`Sym` bookkeeping. |
| Boolean codomain | real-valued `f`, plus predicate `BooleanOnSlice k f : ∀ S, S.card = k → f S = 0 ∨ f S = 1` | `{0,1} ⊆ ℝ` is the natural target when the defining property is agreement with a real polynomial. |
| Degree `≤ d` | `SliceDegreeLE`: `∃ p : MvPolynomial (Fin n) ℝ` with `p.totalDegree ≤ d`, `p` multilinear (`∀ μ ∈ p.support, ∀ i, μ i ≤ 1`), and `f S = MvPolynomial.eval (sliceIndicator S) p` for all `S` on the slice | This is the standard "degree of a Boolean function on the slice". Degree is not well-defined pointwise (many polynomials agree on the slice) but "degree `≤ d`" is. Multilinearity clause added to match the theorem's wording; it is WLOG. |
| `m`-junta | `JuntaOnSlice`: `∃ J, J.card ≤ m ∧ ∀ S T on the slice, S ∩ J = T ∩ J → f S = f T` | "value depends only on `S ∩ J`", stated as an indistinguishability condition rather than via an external `g : {0,1}^m → ℝ` (equivalent, fewer moving parts). |
| `m(d)` | existential `∃ m : ℕ, …` inside the positive theorem | Matches "there is a constant `m(d)`". An explicit `m : ℕ → ℕ` would also be fine; the paper's bound is `2^{Θ(d)}`, not pinned here. |
| `n, k, d`, ambient set | all plain `ℕ`, coordinates `Fin n`; `n` re-quantified inside each theorem | Keeps the two size regimes (`k ≥ 2d` vs `k < 2d`) visible as hypotheses `2*d ≤ k` / `k < 2*d`, and `n ≥ 2k` as `2*k ≤ n`. |
| Explicit family | included, as `filmusFamily d k ℓ n` built from `consecBlock (min d k) i n` (runs of `e = min d k` consecutive coordinates); indexed by number of blocks `ℓ`, with `n` and `ℓ` existentially chosen so that `ℓ·e > m`, `n ≥ 2k`, `n ≥ 2·ℓ·e` | The "`(i-1)e+j`" indexing is exactly "`ℓ` disjoint length-`e` consecutive blocks"; `consecBlock` realizes that with no `Fin`-arithmetic proof obligations. |

## Uncertainties / caveats

- **Product-of-sums vs sum-of-products.** The task writes the family as
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. Taken literally that is
  `∏_i |B_i ∩ S|`, which is **not** `{0,1}`-valued on the slice in general
  (e.g. `|B_1 ∩ S| = 2`), so it is not a Boolean degree-`d` function. The
  construction that actually works (and what the source paper uses, up to an
  indexing typo there too) is the **sum of products**
  `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` = "some length-`e` block is fully
  contained in `S`". Since `1 ≤ k < 2d` gives `2·min d k > k`, at most one block
  fits in a `k`-set, so this sum is `{0,1}`-valued, and each product has degree
  `e = min d k ≤ d`. **I formalized the sum-of-products version** as
  `filmusFamily`; the doc-comments flag this.

- **"not `ℓe`-juntas".** As literally phrased this is false for disjoint
  consecutive blocks: `filmusFamily` reads only the `ℓe` coordinates
  `{x : x.val < ℓe}`, so it *is* an `ℓe`-junta (take `J` = those coordinates).
  The meaningful statement is that it depends essentially on **all** `ℓe` of
  them, hence is not an `(ℓe − 1)`-junta, and `ℓ` is unbounded — which defeats
  every fixed `m`. I encoded this as `m < ℓ * min d k` together with
  `¬ JuntaOnSlice k m (filmusFamily …)`.

- **Mathlib identifiers** (from memory, not compiler-checked):
  `MvPolynomial (Fin n) ℝ`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `MvPolynomial.support` (elements `μ : Fin n →₀ ℕ`, `μ i : ℕ`),
  `Finset.univ.filter`, `Finset.range`, `∑ i ∈ …` big-operator notation,
  `Finset.card`, `∩` on `Finset`, `⊆` on `Finset` with its `Decidable` instance.
  I believe there is no dedicated Mathlib notion of "Boolean degree-`d` function
  on the slice" or "junta", so I defined them.

- The `if consecBlock … ⊆ S` and the `Finset.univ.filter` predicate rely on
  `Decidable` instances being found automatically (`Nat` comparisons, `Finset`
  subset). If elaboration complains, wrapping with `Classical.dec` /
  `open Classical` fixes it without changing the statement.
