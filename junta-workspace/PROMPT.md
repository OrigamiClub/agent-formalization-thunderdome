# Boolean degree-d functions on the slice are juntas — 100-agent formalization sweep

Run date: 2026-08-28. Protocol: statement-only formalizations (`:= by sorry`), no
bridging/comparison pass; all 100 files afterwards compiled against the pinned
Lean/Mathlib checkout (`leanprover/lean4:v4.29.0-rc3`, Mathlib
`777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`). Scope: **each agent chooses** which
part(s) of the theorem to state.

## Target

> **Theorem 1.1.** Let `d ≥ 1`. There exists a constant `m(d)` such that the
> following holds. If `k ≥ 2d` then for any `n ≥ 2k`, every Boolean degree-`d`
> function on the slice `binom([n], k)` (subsets of `{1,…,n}` of size exactly `k`)
> is an `m(d)`-junta.
> Conversely, if `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a
> Boolean degree-`d` function on `binom([n], k)` which is not an `m`-junta.
> The converse is witnessed by functions of the form
> `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e + j} )` with `e = min(d, k)` (indices
> partitioned into `ℓ` blocks of size `e`); for `n ≥ 2ℓe` these are not
> `ℓe`-juntas.

Background terms:
- **slice `binom([n],k)`**: `{ S ⊆ {1,…,n} : |S| = k }`.
- **Boolean function on the slice**: `f : binom([n],k) → {0,1}` (range in `{0,1}`).
- **degree ≤ d**: `f` agrees on the slice with a multilinear real polynomial in
  `x_1,…,x_n` of total degree `≤ d` (i.e. `f(S) = P(1_S)` for the indicator
  vector `1_S`). Equivalent characterisations exist (Fourier support on the first
  `d` levels of the Johnson scheme; all `(d+1)`-fold discrete derivatives vanish).
- **`m`-junta**: `∃ J ⊆ [n]` with `|J| ≤ m` such that `f(S)` depends only on
  `S ∩ J` — i.e. `S ∩ J = T ∩ J ⇒ f(S) = f(T)` for all `S,T` in the slice.

## Exact prompt given to each agent

> You are agent {NNN} in an independent formalization diversity study. You are
> context-isolated: produce your answer with no coordination with any other agent.
>
> TASK: Produce a Lean 4 formalization of the *statement* of the theorem below.
> Statement only — end every theorem with `:= by sorry`. Do NOT prove anything.
> You do NOT have a Lean compiler; work from knowledge of Mathlib. You may state
> one direction, both directions, and/or the explicit witnessing family — YOUR
> CHOICE; say what you chose in the note.
>
> THEOREM (Boolean constant-degree functions on the slice are juntas; Filmus–
> Ihringer):
> Let d ≥ 1. There is a constant m(d) such that: if k ≥ 2d then for every n ≥ 2k,
> every Boolean degree-d function on the slice binom([n],k) is an m(d)-junta.
> Conversely, if 1 ≤ k < 2d then for every m there exist n ≥ 2k and a Boolean
> degree-d function on binom([n],k) that is not an m-junta; witnessed by functions
> ∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j}) with e = min(d,k), which for n ≥ 2ℓe are
> not ℓe-juntas.
>
> Terms: the slice binom([n],k) is {S ⊆ {1,…,n} : |S| = k}. A Boolean function on
> it has values in {0,1}. It has degree ≤ d if it agrees on the slice with a
> multilinear real polynomial of total degree ≤ d evaluated at the indicator
> vector. It is an m-junta if there is a set J of ≤ m coordinates such that its
> value depends only on S ∩ J.
>
> YOUR ENCODING CHOICES ARE YOURS TO MAKE: representation of the slice
> (`{S : Finset (Fin n) // S.card = k}`, a `Finset (Finset (Fin n))`, `Sym`,
> subtype of `Set`, …); Boolean codomain (`{0,1} ⊆ ℝ`, `Bool`, `Fin 2`, `ZMod 2`,
> a `Prop`-valued predicate); how "degree ≤ d" is defined (via `MvPolynomial
> (Fin n) ℝ` and `totalDegree`; via restriction of a function on the hypercube;
> via Johnson/Fourier levels; via vanishing `(d+1)`-fold derivatives; or a Mathlib
> notion if you believe one exists — name it as best you can); how "m-junta" is
> defined; whether `m(d)` is an existential inside the statement or an explicit
> `m : ℕ → ℕ`; how `n`, `k`, `d` and the ambient coordinate set are carried;
> whether the explicit family is included and how its indexing is set up.
>
> DELIVERABLES — write exactly two files:
> 1. `junta-workspace/formalizations/agent_{NNN}.lean` — imports, any auxiliary
>    definitions, and the `theorem … := by sorry`. Self-contained.
> 2. `junta-workspace/formalizations/agent_{NNN}.md` — short note: which part(s)
>    you stated, encoding decisions and why, uncertainties (e.g. guessed Mathlib
>    identifiers).
>
> Do not read any other agent's files. Do not create any other files. When both
> files are written, reply with a one-line summary of your chosen encoding.
