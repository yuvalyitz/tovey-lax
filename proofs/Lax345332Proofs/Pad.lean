import Mathlib.Tactic
import Lax345332Proofs.GadgetOcc

/-!
# Padding short clauses

A formula whose clauses have at most three literals, over variables below `B`, is padded to
clauses of exactly three literals: every missing literal is `¬y` for a fresh `y` that a
private copy of the gadget forces to be true. Occurrence counts below `B` are unchanged and
every new variable occurs at most four times.
-/

namespace Lax345332Proofs.Pad

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat Lax345332Proofs.Occ Lax345332Proofs.Gadget

/-! ### Evaluation -/

theorem eval_cons (C : Clause) (F : Formula) (ρ : Assignment) :
    eval (C :: F) ρ = ((C.any fun l => l.eval ρ) && eval F ρ) := by simp [eval]

theorem eval_append (F G : Formula) (ρ : Assignment) :
    eval (F ++ G) ρ = (eval F ρ && eval G ρ) := by simp [eval]

theorem eval_flatMap {α : Type} (l : List α) (f : α → Formula) (ρ : Assignment) :
    eval (l.flatMap f) ρ = l.all fun a => eval (f a) ρ := by
  simp [eval, List.all_flatMap]

theorem eval_iff (F : Formula) (ρ : Assignment) :
    eval F ρ = true ↔ ∀ C ∈ F, (C.any fun l => l.eval ρ) = true := by simp [eval]

theorem any_congr {C : Clause} {ρ σ : Assignment} (h : ∀ l ∈ C, ρ l.index = σ l.index) :
    (C.any fun l => l.eval ρ) = C.any fun l => l.eval σ := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [List.any_cons]
      rw [ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]
      simp [Literal.eval, h l List.mem_cons_self]

theorem mem_getD {G : Formula} {k : ℕ} (hk : k < G.length) : G.getD k [] ∈ G := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

theorem exists_getD {G : Formula} {C : Clause} (h : C ∈ G) : ∃ k < G.length, G.getD k [] = C := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk, e]⟩

/-! ### Satisfiability -/

theorem pads_false {B k n : ℕ} {τ : Assignment} (h : ∀ t < 3, τ (ybase B k t) = true) :
    ((pads B k n).any fun l => l.eval τ) = false := by
  rw [List.any_eq_false]
  intro l hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
  have := h t (by have := List.mem_range.mp ht; omega)
  simp [Literal.eval, this]

theorem sat_of_pad {B : ℕ} {G : Formula} {τ : Assignment} (h : eval (pad B G) τ = true) :
    eval G τ = true := by
  rw [eval_iff]
  intro C hC
  obtain ⟨k, hk, rfl⟩ := exists_getD hC
  rw [pad, eval_flatMap, List.all_eq_true] at h
  have hu := h k (List.mem_range.mpr hk)
  rw [unit, eval_cons, eval_append, eval_append] at hu
  simp only [Bool.and_eq_true] at hu
  obtain ⟨hm, ⟨h0, h1⟩, h2⟩ := hu
  have hy : ∀ t < 3, τ (ybase B k t) = true := by
    intro t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact gadget_forces h0
    · exact gadget_forces h1
    · exact gadget_forces h2
  rw [List.any_append, pads_false hy, Bool.or_false] at hm
  exact hm

/-- The values the gadget variables take. -/
def pat (c : ℕ) : Bool := decide (c = 0 ∨ c = 6 ∨ c = 9)

/-- An assignment below `B`, extended to satisfy every gadget. -/
def extend (B : ℕ) (σ : Assignment) : Assignment :=
  fun i => if i < B then σ i else pat ((i - B) % 10)

theorem eval_gadget_extend (B k t : ℕ) (σ : Assignment) :
    eval (gadget (ybase B k t)) (extend B σ) = true := by
  have h : ∀ c < 10, extend B σ (ybase B k t + c) = pat c := by
    intro c hc
    have h1 : ¬ ybase B k t + c < B := by unfold ybase; omega
    have h2 : (ybase B k t + c - B) % 10 = c := by unfold ybase; omega
    simp only [extend, if_neg h1, h2]
  rw [eval_gadget]
  have h0 := h 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega)]
  decide

theorem pad_of_sat {B : ℕ} {G : Formula} {σ : Assignment}
    (hvar : ∀ C ∈ G, ∀ l ∈ C, l.index < B) (h : eval G σ = true) :
    eval (pad B G) (extend B σ) = true := by
  rw [pad, eval_flatMap, List.all_eq_true]
  intro k hk
  have hk := List.mem_range.mp hk
  have hC := mem_getD hk
  rw [unit, eval_cons, eval_append, eval_append, eval_gadget_extend, eval_gadget_extend,
    eval_gadget_extend]
  simp only [Bool.and_true, List.any_append, Bool.or_eq_true]
  left
  rw [any_congr (σ := σ) fun l hl => by simp [extend, hvar _ hC l hl]]
  exact (eval_iff G σ).mp h _ hC

theorem pad_sat {B : ℕ} {G : Formula} (hvar : ∀ C ∈ G, ∀ l ∈ C, l.index < B) :
    Satisfiable G ↔ Satisfiable (pad B G) :=
  ⟨fun ⟨_, h⟩ => ⟨_, pad_of_sat hvar h⟩, fun ⟨τ, h⟩ => ⟨τ, sat_of_pad h⟩⟩

/-! ### Shape -/

theorem pad_length {B : ℕ} {G : Formula} (hlen : ∀ C ∈ G, C.length ≤ 3) :
    ∀ C ∈ pad B G, C.length = 3 := by
  intro C hC
  obtain ⟨k, hk, hC⟩ := List.mem_flatMap.mp hC
  have hk := List.mem_range.mp hk
  have := hlen _ (mem_getD hk)
  rw [unit, List.mem_cons] at hC
  rcases hC with rfl | hC
  · rw [List.length_append, pads, List.length_map, List.length_range]; omega
  · simp only [List.mem_append] at hC
    rcases hC with (hC | hC) | hC <;> exact gadget_length _ _ hC

end Lax345332Proofs.Pad
