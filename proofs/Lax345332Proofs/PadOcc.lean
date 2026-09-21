import Mathlib.Tactic
import Lax345332Proofs.Pad

/-!
# Padding keeps every variable at four occurrences
-/

namespace Lax345332Proofs.Pad

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat Lax345332Proofs.Occ Lax345332Proofs.Gadget

theorem cnt_append (C D : Clause) (i : ℕ) : cnt (C ++ D) i = cnt C i + cnt D i := by
  simp [cnt]

theorem cnt_eq_zero {C : Clause} {i : ℕ} (h : ∀ l ∈ C, l.index ≠ i) : cnt C i = 0 := by
  simp only [cnt, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro l hl; simpa using h l hl

theorem cnt_map_range (n : ℕ) (f : ℕ → Literal) (i : ℕ) :
    cnt ((List.range n).map f) i =
      ((List.range n).map fun t => if (f t).index = i then 1 else 0).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, cnt_append, ih, List.map_append, List.sum_append]
      congr 1
      by_cases h : (f n).index = i <;> simp [cnt, h]

theorem occ_eq_sum_getD (G : Formula) (i : ℕ) :
    occurrences G i = ((List.range G.length).map fun k => cnt (G.getD k []) i).sum := by
  have : G = (List.range G.length).map fun k => G.getD k [] := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2; simp [h1]
  conv_lhs => rw [this]
  rw [occ_map]

theorem occ_unit (B k : ℕ) (C : Clause) (i : ℕ) :
    occurrences (unit B k C) i = cnt C i + cnt (pads B k C.length) i +
      (occurrences (gadget (ybase B k 0)) i + occurrences (gadget (ybase B k 1)) i +
        occurrences (gadget (ybase B k 2)) i) := by
  rw [unit, occ_cons, cnt_append, occ_append, occ_append]

/-- What a unit contributes to a variable at or above `B`. -/
theorem unit_tail (B k n i : ℕ) (hi : B ≤ i) :
    cnt (pads B k n) i + (occurrences (gadget (ybase B k 0)) i +
      occurrences (gadget (ybase B k 1)) i + occurrences (gadget (ybase B k 2)) i) ≤ 4 ∧
    ((i - B) / 30 ≠ k → cnt (pads B k n) i + (occurrences (gadget (ybase B k 0)) i +
      occurrences (gadget (ybase B k 1)) i + occurrences (gadget (ybase B k 2)) i) = 0) := by
  rw [pads, cnt_map_range]
  by_cases hin : B + 30 * k ≤ i ∧ i < B + 30 * k + 30
  · obtain ⟨c, hc, t0, ht0, hic⟩ : ∃ c < 10, ∃ t0 < 3, i = ybase B k t0 + c :=
      ⟨(i - (B + 30 * k)) % 10, by omega, (i - (B + 30 * k)) / 10, by omega, by unfold ybase; omega⟩
    have hP : ((List.range (3 - n)).map fun t =>
        if (⟨ybase B k t, false⟩ : Literal).index = i then 1 else 0).sum ≤ if c = 0 then 1 else 0 := by
      apply sum_range_le_one _ t0
      · intro t _ hne
        rw [if_neg]; simp only [ybase] at hic ⊢; omega
      · intro t _
        by_cases h : (⟨ybase B k t, false⟩ : Literal).index = i
        · have : c = 0 := by simp only [ybase] at hic h; omega
          subst this; split_ifs <;> omega
        · simp [h]
    have hA := gadget_occ_in (ybase B k t0) c hc
    rw [← hic] at hA
    refine ⟨?_, fun hne => absurd hne (by rw [not_not]; omega)⟩
    have : t0 = 0 ∨ t0 = 1 ∨ t0 = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have h1 := gadget_occ_out (ybase B k 1) i (by simp only [ybase] at hic ⊢; omega)
      have h2 := gadget_occ_out (ybase B k 2) i (by simp only [ybase] at hic ⊢; omega)
      split_ifs at hP hA <;> omega
    · have h1 := gadget_occ_out (ybase B k 0) i (by simp only [ybase] at hic ⊢; omega)
      have h2 := gadget_occ_out (ybase B k 2) i (by simp only [ybase] at hic ⊢; omega)
      split_ifs at hP hA <;> omega
    · have h1 := gadget_occ_out (ybase B k 0) i (by simp only [ybase] at hic ⊢; omega)
      have h2 := gadget_occ_out (ybase B k 1) i (by simp only [ybase] at hic ⊢; omega)
      split_ifs at hP hA <;> omega
  · have hP : ((List.range (3 - n)).map fun t =>
        if (⟨ybase B k t, false⟩ : Literal).index = i then 1 else 0).sum = 0 := by
      apply sum_range_eq_zero
      intro t ht
      rw [if_neg]; simp only [ybase]; omega
    have h0 := gadget_occ_out (ybase B k 0) i (by simp only [ybase]; omega)
    have h1 := gadget_occ_out (ybase B k 1) i (by simp only [ybase]; omega)
    have h2 := gadget_occ_out (ybase B k 2) i (by simp only [ybase]; omega)
    exact ⟨by omega, fun _ => by omega⟩

theorem pad_occ {B : ℕ} {G : Formula} (hvar : ∀ C ∈ G, ∀ l ∈ C, l.index < B)
    (hocc : ∀ i, occurrences G i ≤ 4) : ∀ i, occurrences (pad B G) i ≤ 4 := by
  intro i
  rw [pad, occ_flatMap]
  by_cases hi : i < B
  · have : ((List.range G.length).map fun k => occurrences (unit B k (G.getD k [])) i) =
        (List.range G.length).map fun k => cnt (G.getD k []) i := by
      apply List.map_congr_left
      intro k _
      rw [occ_unit]
      have hp : cnt (pads B k (G.getD k []).length) i = 0 :=
        cnt_eq_zero fun l hl => by
          obtain ⟨t, -, rfl⟩ := List.mem_map.mp hl
          simp only [ybase]; omega
      have h0 := gadget_occ_out (ybase B k 0) i (by simp only [ybase]; omega)
      have h1 := gadget_occ_out (ybase B k 1) i (by simp only [ybase]; omega)
      have h2 := gadget_occ_out (ybase B k 2) i (by simp only [ybase]; omega)
      omega
    rw [this, ← occ_eq_sum_getD]
    exact hocc i
  · have hC : ∀ k < G.length, cnt (G.getD k []) i = 0 := fun k hk =>
      cnt_eq_zero fun l hl => by have := hvar _ (mem_getD hk) l hl; omega
    apply sum_range_le_one _ ((i - B) / 30)
    · intro k hk hne
      rw [occ_unit, hC k hk]
      have := (unit_tail B k (G.getD k []).length i (by omega)).2 (fun h => hne h.symm)
      omega
    · intro k hk
      rw [occ_unit, hC k hk]
      have := (unit_tail B k (G.getD k []).length i (by omega)).1
      omega

end Lax345332Proofs.Pad
