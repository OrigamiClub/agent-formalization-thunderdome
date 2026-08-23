import Mathlib

/-!
Actually-compiled bridge checks for the Glaisher equivalence-class claims in
REPORT.md. Each `example`/`theorem` below is one specific cross-cluster bridge.
-/

variable (n k : ℕ)

-- Tier 1: Set.ncard (set-builder) vs Nat.card (subtype) — same underlying type.
example :
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, ¬ k ∣ i}
      = Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} := rfl

-- Tier 2a: Finset.card of a `Finset.univ.filter` vs Nat.card of the subtype,
-- for a DECIDABLE predicate (needed for `Finset.filter`/`Fintype.card_subtype`).
example (hk : 2 ≤ k) :
    (Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, ¬ k ∣ i)).card
      = Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

-- Tier 2b: the "unscoped" condition (∀ i : ℕ, count i < k) is equivalent to the
-- "scoped" condition (∀ i ∈ parts, count i < k), given k ≥ 2 (in fact k ≥ 1 suffices).
example (s : Multiset ℕ) (hk : 1 ≤ k) :
    (∀ i : ℕ, s.count i < k) ↔ (∀ i ∈ s, s.count i < k) := by
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i ∈ s
    · exact h i hi
    · simpa [Multiset.count_eq_zero_of_notMem hi] using hk

-- Tier 3: `Nat.Partition n` is literally structurally the subtype
-- `{s : Multiset ℕ // (∀ i ∈ s, 0 < i) ∧ s.sum = n}` used by the raw-Multiset agents —
-- an explicit `Equiv` between them, and cardinality transport across it.
def partitionEquivSubtype :
    Nat.Partition n ≃ {s : Multiset ℕ // (∀ i ∈ s, 0 < i) ∧ s.sum = n} where
  toFun p := ⟨p.parts, fun i hi => p.parts_pos hi, p.parts_sum⟩
  invFun s := ⟨s.1, fun {i} hi => s.2.1 i hi, s.2.2⟩
  left_inv p := by cases p; rfl
  right_inv s := by obtain ⟨s, _, _⟩ := s; rfl

example :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i}
      = Nat.card {s : {s : Multiset ℕ // (∀ i ∈ s, 0 < i) ∧ s.sum = n} //
                    ∀ i ∈ s.1, ¬ k ∣ i} := by
  apply Nat.card_congr
  exact (partitionEquivSubtype n).subtypeEquiv (fun p => Iff.rfl)
