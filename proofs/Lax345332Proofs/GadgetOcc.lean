import Mathlib.Tactic
import Lax345332Proofs.Gadget
import Lax345332Proofs.Occ

namespace Lax345332Proofs.Gadget

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat Lax345332Proofs.Occ

theorem gadget_occ_out (g i : ℕ) (h : i < g ∨ g + 10 ≤ i) : occurrences (gadget g) i = 0 := by
  have h0 : g ≠ i := by omega
  have h1 : g + 1 ≠ i := by omega
  have h2 : g + 2 ≠ i := by omega
  have h3 : g + 3 ≠ i := by omega
  have h4 : g + 4 ≠ i := by omega
  have h5 : g + 5 ≠ i := by omega
  have h6 : g + 6 ≠ i := by omega
  have h7 : g + 7 ≠ i := by omega
  have h8 : g + 8 ≠ i := by omega
  have h9 : g + 9 ≠ i := by omega
  simp [gadget, occurrences, List.range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem gadget_occ_in (g c : ℕ) (hc : c < 10) :
    occurrences (gadget g) (g + c) ≤ if c = 0 then 3 else 4 := by
  interval_cases c <;>
    simp [gadget, occurrences, List.range_succ, Nat.add_assoc]

end Lax345332Proofs.Gadget
