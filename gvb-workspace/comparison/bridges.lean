import Mathlib

/-!
Actually-compiled bridge checks for the GVB equivalence-class claims in REPORT.md.
Each `example` is one specific cross-cluster bridge, proved (not `sorry`).
-/

-- Bridge 1: hammingDist vs. the inline `Finset.filter`-cardinality encoding used
-- by the other cluster, for a concrete choice of `n q`.
example (n q : ℕ) (x y : Fin n → Fin q) :
    hammingDist x y = (Finset.univ.filter (fun i => x i ≠ y i)).card := rfl

-- Bridge 2: `Nat.choose` dot-notation vs. prefix application (pure notation).
example (n i : ℕ) : (n - 1).choose i = Nat.choose (n - 1) i := rfl

-- Bridge 3: `0 < n` vs `1 ≤ n` for Nat (the two hypothesis phrasings used across agents).
example (n : ℕ) : (0 < n) = (1 ≤ n) := rfl

-- Bridge 4: legacy `∑ i in s` vs current `∑ i ∈ s` binder notation — this is the ONE
-- claim from the report that this environment actually REJECTS (see combined_all.lean
-- compile log): `in` no longer parses in this Mathlib revision. Recorded as FAILED below
-- (commented out, since it is a parse error, not a proof goal):
-- example (d q n : ℕ) :
--     (∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
--   = (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) := rfl
-- ^ fails to PARSE (not just fails to prove): "unexpected token 'in'; expected ','"
