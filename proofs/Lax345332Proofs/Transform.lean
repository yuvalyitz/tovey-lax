import Mathlib.Tactic
import Lax345332Proofs.SplitShape

/-!
# The reduction on formulas

`transform F` is a (3,4) formula that is satisfiable exactly when `F` is.
-/

namespace Lax345332Proofs.Transform

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat Lax345332Proofs.Occ Lax345332Proofs.Pad
open Lax345332Proofs.Split

variable {V N : ℕ}

theorem mem_chainClause {o : ℕ} {C : Clause} {i : ℕ} {l : Literal} (hl : l ∈ chainClause V N o C i) :
    (i ≠ 0 ∧ l.index = zv V N (o + i - 1)) ∨ l.index = wv V (C.getD i dflt).index (o + i) ∨
      l.index = zv V N (o + i) := by
  simp only [chainClause, List.mem_append, List.mem_singleton] at hl
  rcases hl with (hl | rfl) | hl
  · by_cases h : i = 0
    · simp [h] at hl
    · simp only [h, if_false, List.mem_singleton] at hl; subst hl; exact Or.inl ⟨h, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · by_cases h : i + 1 = C.length
    · simp [h] at hl
    · simp only [h, if_false, List.mem_singleton] at hl; subst hl; exact Or.inr (Or.inr rfl)

theorem chainClause_length (o : ℕ) (C : Clause) (i : ℕ) : (chainClause V N o C i).length ≤ 3 := by
  simp only [chainClause, List.length_append, List.length_singleton]
  split_ifs <;> simp

theorem chains_shape : ∀ (F : Formula) (o : ℕ), o + size F ≤ N →
    (∀ C ∈ F, ∀ l ∈ C, l.index < V) →
    ∀ D ∈ chains V N o F, D.length ≤ 3 ∧ ∀ l ∈ D, l.index < V * N + N := by
  intro F
  induction F with
  | nil => intro _ _ _ D hD; simp [chains] at hD
  | cons C F ih =>
      intro o hsz hV D hD
      simp only [size, List.map_cons, List.sum_cons] at hsz
      rw [chains, List.mem_append] at hD
      rcases hD with hD | hD
      · by_cases h0 : C.length = 0
        · rw [chainClauses, if_pos h0, List.mem_singleton] at hD; subst hD; simp
        · rw [chainClauses, if_neg h0] at hD
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hD
          have hi := List.mem_range.mp hi
          refine ⟨chainClause_length o C i, fun l hl => ?_⟩
          have hw := wv_lt (N := N) (hV C List.mem_cons_self _ (getD_mem hi)) (show o + i < N by omega)
          rcases mem_chainClause hl with ⟨_, e⟩ | e | e <;> rw [e]
          · unfold zv; omega
          · omega
          · unfold zv; omega
      · exact ih (o + C.length) (by simp only [size]; omega)
          (fun E hE => hV E (List.mem_cons_of_mem _ hE)) D hD

theorem cycles_shape : ∀ D ∈ cycles V N, D.length ≤ 3 ∧ ∀ l ∈ D, l.index < V * N + N := by
  intro D hD
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hD
  have hk := List.mem_range.mp hk
  have hVp : 0 < V := Nat.pos_of_ne_zero fun h => by simp [h] at hk
  have hNp : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hk
  refine ⟨by simp, fun l hl => ?_⟩
  have hw := wv_lt (N := N) (Nat.mod_lt k hVp) (next_lt (p := k / V) hNp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · show k < V * N + N; omega
  · show wv V (k % V) (next N (k / V)) < V * N + N; omega

theorem split_shape (F : Formula) :
    ∀ D ∈ split F, D.length ≤ 3 ∧ ∀ l ∈ D, l.index < bound F * size F + size F := by
  intro D hD
  rw [split, List.mem_append] at hD
  rcases hD with hD | hD
  · exact chains_shape F 0 (by omega) (fun C hC l hl => index_lt_bound hC hl) D hD
  · exact cycles_shape D hD

/--
---
conclusion: Lax345332.Construction.transform_isThreeFour
---
Padding makes every clause three literals long. Below the padding base the occurrence counts
are those of the split formula, at most three; above it a variable belongs to one gadget of
one clause, where it occurs at most four times, the forced variable three times in the
gadget and once as padding.
-/
theorem transform_isThreeFour (F : Formula) : IsThreeFour (transform F) :=
  ⟨pad_length fun C hC => (split_shape F C hC).1,
    pad_occ (fun C hC => (split_shape F C hC).2) (split_occ F)⟩

/--
---
conclusion: Lax345332.Construction.transform_sat
---
Splitting: an assignment of `F` is copied to every position and the link after a literal is
set to "no literal so far is true"; conversely the cycle makes all copies of a variable
equal, and a chain with all literals false propagates a true link into its last clause.
Padding: the gadgets force the padding literals false, and can always be satisfied.
-/
theorem transform_sat (F : Formula) : Satisfiable F ↔ Satisfiable (transform F) :=
  (split_sat F).trans (pad_sat fun C hC => (split_shape F C hC).2)

end Lax345332Proofs.Transform
