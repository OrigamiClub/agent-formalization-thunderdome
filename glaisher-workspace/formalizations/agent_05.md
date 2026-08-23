# Glaisher's theorem — formalization notes (agent_05)

I represented a partition of `n` explicitly rather than via `Nat.Partition`, to avoid
relying on uncertain recollection of that structure's exact field names: `IsPartition n s`
holds for `s : Multiset ℕ` when every element of `s` is positive and `s.sum = n`. This
is definitionally the same data `Nat.Partition` bundles, just as a plain predicate on
multisets, which keeps the statement self-contained.

The two conditions are encoded directly on the multiset: "no part divisible by k" is
`∀ x ∈ s, ¬ k ∣ x` (set `GlaisherA`), and "every part occurs fewer than k times" is
`∀ x ∈ s, s.count x < k` (set `GlaisherB`), using `Multiset.count` for multiplicity.
Both sets are subsets of `Multiset ℕ`, further cut down by `IsPartition n`.

I stated the theorem as a cardinality equality, `Nat.card (GlaisherA k n) = Nat.card (GlaisherB k n)`,
for `k ≥ 2` and all `n`, rather than as an explicit bijection, since `Nat.card` gives a clean
statement without needing to construct or name the (well-known, but nontrivial-to-encode)
bijective map. I did not separately assert finiteness of these sets (it's true but not needed
to state the equality); `Nat.card` defaults to `0` on infinite types, which is harmless here
since both sets are in fact finite for each `n`.
