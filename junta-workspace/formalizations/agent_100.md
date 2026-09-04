# agent_100 — formalization note

## What is stated

Three `sorry`-terminated theorems, statement only:

1. `filmus_ihringer_junta` — the **forward** direction: `d ≥ 1 ⟹ ∃ m(d)`, then for all
   `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`d` function on the slice is an
   `m(d)`-junta.
2. `filmus_ihringer_sharp` — the **converse** direction as a pure existential, over the
   full range `1 ≤ k < 2d`: for every `m` there is a slice and a Boolean degree-`d`
   function on it that is not an `m`-junta.
3. `filmus_ihringer_witness` — the **explicit witnessing family**, stated for `1 ≤ k ≤ d`
   (where `e = min d k = k`): the product-of-linear-forms polynomial `witnessPoly`,
   whose induced slice function is Boolean, degree `≤ d`, and not an `m`-junta for any
   `m < kℓ`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`, the
  most direct rendering of `{S ⊆ [n] : |S| = k}`; coordinate set carried as `Fin n`.
- **Boolean codomain**: functions into `ℝ` with a separate `IsBoolean` predicate
  (`∀ S, f S = 0 ∨ f S = 1`). Keeping the codomain `ℝ` makes "agrees with a real
  polynomial" statable without a coercion dance.
- **Degree `≤ d`** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`,
  and `f S = eval (indicator S.1) p` for all slice points, where `indicator` is the
  `0/1` real indicator vector. No multilinearity constraint: on `0/1` inputs a polynomial
  agrees with its multilinearization, which does not increase total degree, so the two
  formulations are equivalent. This is the Nisan–Szegedy / Filmus "Boolean degree `d`"
  notion. I did not find a dedicated Mathlib notion for slice/hypercube function degree,
  hence the `MvPolynomial` route.
- **`m`-junta** (`IsJunta f m`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S ∩ J = T ∩ J → f S = f T`. Standard "value determined by `S ∩ J`" phrasing.
  `IsJunta` is monotone in `m`, so "not a `(kℓ-1)`-junta" ⇒ "not an `m`-junta for all
  `m < kℓ`"; I state the `∀ m < kℓ` form directly.
- **`m(d)`**: existential *inside* the statement (`∃ m : ℕ, ∀ k …`), placed under
  `∀ d`, so `m` depends only on `d` as required.
- **`n`, `k`, `d`**: explicit `ℕ` hypotheses with the stated inequalities; ambient
  coordinate set is `Fin n`.

## The explicit family — deviation from the literal formula

The task writes the witness as `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d,k)`,
"not `ℓe`-juntas". Read literally (product over `ℓ` factors) this has total degree `ℓ`,
which cannot be `≤ d` for large `ℓ`, and for `ℓ > k` the induced slice function is
identically `0` (a `0`-junta). I therefore read it as **`e` outer factors of inner width
`ℓ`**: `witnessPoly n ℓ e = ∏_{i<e}(∑_{a ∈ block i} X a)` with `e` disjoint blocks
`block i` of size `ℓ`. Total degree `e = min d k ≤ d`; on the slice the value is
`∏_{i<e} |S ∩ block i|`.

For this to be `{0,1}`-valued I restricted theorem 3 to `1 ≤ k ≤ d`, where `e = k` and the
product is exactly the indicator that `S` is a transversal (one element per block) of the
`k` blocks — manifestly Boolean, and dependent on all `kℓ` block coordinates, hence not an
`m`-junta for `m < kℓ`. For `d < k < 2d` the raw product is not Boolean on the slice
(e.g. `d=2, k=3`: `S` with two points in one block gives value `2`); Filmus–Ihringer's
construction there needs an extra step which I did not attempt to encode. The **converse
statement (theorem 2) is stated for the full range `1 ≤ k < 2d`** as a plain existential,
which is the correct and complete tightness claim; theorem 3 is the explicit witness only
for the `k ≤ d` part. "not `ℓe`-juntas" is rendered as "not an `m`-junta for every
`m < kℓ`" (the function *is* trivially a `kℓ`-junta, since it depends on exactly those
`kℓ` coordinates).

## Uncertainties / guessed identifiers

- `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.X`, `Finset.filter`,
  `Finset.range`, and the `∏ i ∈ s, _` / `∑ a ∈ s, _` big-operator notation are all
  believed current in Mathlib but not compiler-checked here.
- `Finset.univ.filter` in `block` relies on automatic `DecidablePred` synthesis for a
  conjunction of `ℕ` comparisons; should be fine, not verified.
- Whether `2 * k * ℓ ≤ n` is the exact threshold intended by "`n ≥ 2ℓe`"; I used
  `2·k·ℓ` (with `e = k`).
