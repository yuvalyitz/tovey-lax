import Lax345332.Construction

/-!
# The forcing gadget

Thirteen clauses on ten variables `y, a₁, b₁, d₁, …, a₃, b₃, d₃` that are satisfiable and
force `y` to be true. `y` occurs three times in them and every other variable four times.
-/

namespace Lax345332Proofs.Gadget

open Lax345332.Construction Lax429075.CNF

/-- The gadget as a Boolean function of its ten variables. -/
def gadgetB (y a1 b1 d1 a2 b2 d2 a3 b3 d3 : Bool) : Bool :=
  (y || a1 || b1) && (y || a2 || b2) && (y || a3 || b3) &&
  (d1 || a1 || !b1) && (d1 || !a1 || b1) && (d1 || !a1 || !b1) &&
  (d2 || a2 || !b2) && (d2 || !a2 || b2) && (d2 || !a2 || !b2) &&
  (d3 || a3 || !b3) && (d3 || !a3 || b3) && (d3 || !a3 || !b3) &&
  (!d1 || !d2 || !d3)

/-- The gadget forces `y`. -/
theorem gadgetB_forces : ∀ y a1 b1 d1 a2 b2 d2 a3 b3 d3 : Bool,
    gadgetB y a1 b1 d1 a2 b2 d2 a3 b3 d3 = true → y = true := by decide

theorem eval_gadget (g : ℕ) (ρ : Assignment) :
    eval (gadget g) ρ = gadgetB (ρ g) (ρ (g+1)) (ρ (g+2)) (ρ (g+3)) (ρ (g+4)) (ρ (g+5))
      (ρ (g+6)) (ρ (g+7)) (ρ (g+8)) (ρ (g+9)) := by
  simp [gadget, eval, Literal.eval, gadgetB, List.range_succ, Bool.and_assoc]
  cases ρ g <;> cases ρ (g+1) <;> cases ρ (g+2) <;> cases ρ (g+3) <;> cases ρ (g+4) <;>
    cases ρ (g+5) <;> cases ρ (g+6) <;> cases ρ (g+7) <;> cases ρ (g+8) <;> cases ρ (g+9) <;> rfl

theorem gadget_forces {g : ℕ} {ρ : Assignment} (h : eval (gadget g) ρ = true) : ρ g = true := by
  rw [eval_gadget] at h; exact gadgetB_forces _ _ _ _ _ _ _ _ _ _ h

theorem gadget_length (g : ℕ) : ∀ C ∈ gadget g, C.length = 3 := by
  simp [gadget, List.range_succ]

end Lax345332Proofs.Gadget
