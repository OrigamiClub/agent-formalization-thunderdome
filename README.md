# agent-formalization-thunderdome

Independent-agent formalization diversity studies: for a given theorem, spawn N
context-isolated agents (N = 20 or 100 so far), have each independently produce a
Lean 4 formalization of the statement (no coordination, no proof required —
`:= by sorry`), then compare the results for equivalence by (1) bridging —
arguing/proving that differently shaped formalizations assert the same thing, and
(2) a lexicographic "looks-good-enough" check — clustering formalizations that are
textually identical after normalization. The 20-agent runs were additionally
**compiled** against a live Lean/Mathlib checkout (`leanprover/lean4:v4.29.0-rc3`,
Mathlib commit `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`) to verify both the
formalizations and the hand-argued bridge claims. The two 100-agent runs skip the
comparison component; of those, the sunflower run was not compiled and the junta
run was compiled against the same pinned checkout.

## Results

### [`gvb-workspace/`](gvb-workspace) — Gilbert–Varshamov bound

- **Low diversity**: all 20 agents converged on the same combinatorial/existential
  form (alphabet `Fin q`, codewords `Fin n → Fin q`, code as `Finset`), differing
  only in cosmetic notation — likely because the prompt spelled the inequality out
  explicitly. One true equivalence class.
- **Compiled**: **18/20 PASS**. Agents 11 and 19 **fail to parse** — they used the
  legacy `∑ i in s` sum-binder syntax, which this Mathlib revision rejects (needs
  `∑ i ∈ s`). A real defect the hand-argument alone didn't catch.
- All Tier-1 (definitional) bridge claims compile via `rfl`.
- Details: [`gvb-workspace/comparison/REPORT.md`](gvb-workspace/comparison/REPORT.md),
  [`gvb_equivalence.csv`](gvb-workspace/comparison/gvb_equivalence.csv),
  [`bridges.lean`](gvb-workspace/comparison/bridges.lean).

### [`glaisher-workspace/`](glaisher-workspace) — Glaisher's theorem

- **Real structural diversity** across three independent axes: partition
  representation (`Nat.Partition n` vs. a raw `Multiset ℕ` predicate defined from
  scratch), cardinality mechanism (`Nat.card` / `Set.ncard` / `Finset.card`), and
  quantifier scope on the multiplicity condition (`∀i∈parts` vs. `∀i`) — 6 distinct
  lexicographic groups.
- All 6 groups bridge to one equivalence class via three escalating tiers: pure
  notation (`rfl`), a short standard lemma (e.g. `Fintype.card_subtype`,
  `Multiset.count_eq_zero_of_notMem`), or a small explicit `Equiv` construction
  (`Nat.Partition n ≃ {s : Multiset ℕ // (∀i∈s,0<i) ∧ s.sum=n}`, since
  `Nat.Partition` is literally that structure under the hood).
- **Compiled**: **20/20 PASS**, and every bridge tier was written as a real proof
  and compiled successfully — including catching and fixing one wrong guessed
  lemma name (`count_eq_zero_of_not_mem` → the real name is
  `count_eq_zero_of_notMem`) via the compiler rather than documentation lookup.
- Details: [`glaisher-workspace/comparison/REPORT.md`](glaisher-workspace/comparison/REPORT.md),
  [`glaisher_equivalence.csv`](glaisher-workspace/comparison/glaisher_equivalence.csv),
  [`bridges.lean`](glaisher-workspace/comparison/bridges.lean).

### [`sunflower-workspace/`](sunflower-workspace) — improved sunflower lemma (log bound)

- **100 agents**, formalization-only (no bridging, not compiled). Target: the
  Alweiss–Lovett–Wu–Zhang / Rao / Bell–Chueluecha–Warnke bound
  `f(k,r) ≤ (C·r·log k)^k`.
- **Very low diversity**, like GVB: **100/100** used `W : Finset (Finset α)` over
  an ambient `[DecidableEq α]`, `Finset.card`, `Real.log` (natural log), an
  outermost `∃ C : ℝ, 0 < C`, a locally-defined core-based sunflower predicate,
  and no nonempty-petal requirement. Zero used `Real.logb 2`, `Nat.log`,
  `Set.ncard`, or a `Set`-with-finiteness representation.
- The one axis with a real modelling decision — the `k ≤ 1` degeneracy of
  `(C·r·log k)^k` (`log 1 = 0` makes the bound false, since `f(1,r) = r`) — split
  **73 / 27**: exclude it with a `2 ≤ k` hypothesis, vs. keep `0 < k` and patch the
  logarithm (`Real.log (k+1)`, 18; `max 1 (Real.log k)`, 9). Other differences
  (explicit `∀∀` vs. `Set.Pairwise` core condition, redundant `Y ⊆ member` clause,
  where `𝒮.card = r` lives, a second `f(k,r)` restatement in 72 files) are
  cosmetic.
- Details: [`sunflower-workspace/REPORT.md`](sunflower-workspace/REPORT.md),
  [`sunflower-workspace/PROMPT.md`](sunflower-workspace/PROMPT.md).

### [`junta-workspace/`](junta-workspace) — Boolean degree-`d` functions on the slice are juntas

- **100 agents**, formalization-only (no bridging), but **compiled**. Target:
  Filmus–Ihringer Theorem 1.1 (arXiv:2203.04760) — for `d ≥ 1` there is a constant
  `m(d)` such that `k ≥ 2d` forces every Boolean degree-`d` function on the slice
  `binom([n],k)` to be an `m(d)`-junta; converse for `1 ≤ k < 2d` with an explicit
  witnessing family. **Each agent chose** which parts to state (74/100 stated all
  three: forward, converse, explicit family).
- **Harder to state** than the earlier targets (no Mathlib "Boolean degree" API;
  "degree-`d` on the slice" and "`m`-junta" both built from scratch) — yet still
  near-total convergence on the parts with a natural rendering: **100/100** on
  real-valued codomain + separate `{0,1}` predicate, the
  `MvPolynomial`/`totalDegree` degree definition, the
  `∃ J, J.card ≤ m ∧ (S∩J = T∩J → f S = f T)` junta predicate, and `∃ m(d)`.
- Real divergence only where the prompt underdetermined: slice representation
  (`Fin n` subtype **84** / side-condition **~9** / `ℕ`-indexed **~9**), how much
  of the two-directional theorem to state, and the witness formula — **35 agents
  independently flagged that the prompt's literal `∏_i(Σ_j x)` is not Boolean on
  the slice and substituted the paper's dual `Σ_i(∏_j x)` form**.
- **Compiled**: **90/100 PASS**. All 10 failures are mechanical and leave the
  theorem statements themselves elaborating: 5× a helper `def` needs
  `noncomputable` (`MvPolynomial` ring is noncomputable), 4× a `Finset (Fin n)`
  vs. `ℕ` binder-coercion slip in the witness family, 1× a stray `open` token.
  Zero wrong propositions.
- Details: [`junta-workspace/REPORT.md`](junta-workspace/REPORT.md),
  [`junta-workspace/PROMPT.md`](junta-workspace/PROMPT.md),
  [`junta-workspace/compile/results.csv`](junta-workspace/compile/results.csv).

## Takeaway

No agent, in any run, formalized a mathematically wrong statement. The runs differ
mainly in how much genuine diversity the prompt left room for: GVB and the
sunflower run spelled the bound out symbolically and got near-total convergence
(one true equivalence class / one shared skeleton), while Glaisher's leaner prompt
produced real structural diversity across 6 groups. Where compilation was run
(both 20-agent runs and the 100-agent junta run) it caught real issues pure
inspection missed — a syntax incompatibility in 2/20 GVB files, a wrong lemma name
during bridge-writing, and 10/100 junta files with a missing `noncomputable`, a
binder-coercion slip, or a stray token — but never a mathematically wrong
statement.
