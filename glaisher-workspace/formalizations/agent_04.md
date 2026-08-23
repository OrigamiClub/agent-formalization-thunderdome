# Glaisher's theorem — formalization notes (agent_04)

I represented "a partition of `n`" using Mathlib's `Nat.Partition n`, a structure bundling a
multiset `parts : Multiset ℕ` with proofs that all parts are positive and that they sum to `n`.
The condition "no part divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`. The condition
"every part occurs fewer than `k` times" is encoded via multiset multiplicity as
`∀ i, p.parts.count i < k` (this is trivially true, and hence imposes no constraint, for any `i`
not actually occurring in `p.parts`, since `count i = 0 < k` when `k ≥ 2`). I stated the theorem
as an equality of `Nat.card` of the two corresponding subtypes of `Nat.Partition n` (rather than
as an explicit bijection), since `Nat.card` sidesteps the need to supply `Fintype`/`Decidable`
instances by hand while still capturing "same cardinality" faithfully for these finite sets. The
statement is universally quantified over `k ≥ 2` and `n : ℕ`, matching the general Glaisher
statement (with `k = 2` recovering Euler's odd/distinct-parts theorem as a special case). One
identifier I was not 100% certain of is the exact field name `parts` and the precise form of the
positivity field in `Nat.Partition`, but I'm fairly confident `parts : Multiset ℕ` together with
`Multiset.count` for multiplicities is correct Mathlib usage.
