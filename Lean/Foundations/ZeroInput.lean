module

public import Std

@[expose] public section

namespace ZeroInput
open Lean.Grind

/-- At a linear contact, its product with the three scalar factors
    is quadratic in the stored pair b, b(b−1). -/
theorem marked_product {R : Type} [CommRing R] (b μ : R) :
    (b-μ) * (b*(b-1)*(32*b+343)) =
    b*(b-1)*(32*(b*(b-1))+(375-32*μ)*b-343*μ) := by grobner

/-- The literal third exceptional row of the new quartic. -/
theorem translated_product {R : Type} [CommRing R] (h : R) :
    let b := h+2401
    let v := h*b
    v*(32*v+77143*h+185220000) = h*(b*(b-1)*(32*b+343)) := by
  dsimp
  grobner

/-- Evaluation of one affine quadratic after homogenization. -/
theorem quadratic_row {R : Type} [CommRing R] (h x y a b c : R) :
    a*(h*x)*(h*y)+b*(h*x)*h+c*h^2 = h^2*(a*x*y+b*x+c) := by grobner

theorem nonzero_row_iff {R : Type} [Field R] (h u : R) (hh : h ≠ 0) :
    h^2*u=0 ↔ u=0 := by
  have hinv := Field.mul_inv_cancel hh
  constructor <;> intro he <;> grobner

/-- The exact projected set obtained by gluing the zero fibre. -/
theorem projection_union {P Q : Rat → Prop} (origin : Q 0)
    (away : ∀ x, x ≠ 0 → (Q x ↔ P x)) (x : Rat) :
    Q x ↔ x = 0 ∨ P x := by
  by_cases hx : x = 0
  · subst x
    exact ⟨fun _ => Or.inl rfl, fun _ => origin⟩
  · rw [away x hx]
    exact ⟨Or.inr, fun h => h.elim (fun e => False.elim (hx e)) id⟩

/-- Consecutive Lucas numbers are preserved by the quadratic norm. -/
theorem lucas_norm {R : Type} [CommRing R] (a x y : R) :
    y^2-a*y*(a*y-x)+(a*y-x)^2 = x^2-a*x*y+y^2 := by grobner

def lucas (a : Int) : Nat → Int × Int
  | 0 => (0,1)
  | n+1 => let (u,v) := lucas a n; (v,a*v-u)

def difference (j : Int) : Nat → Int × Int
  | 0 => (0,0)
  | n+1 => let (u,v) := difference j n; (v,(j+2)*v-u+(n:Int)+1)

/-- An integer divided difference gives both Lucas terms over every modulus. -/
theorem lucas_divided (j : Int) (n : Nat) :
    (lucas (j+2) n).1 = (n:Int)+j*(difference j n).1 ∧
    (lucas (j+2) n).2 = (n:Int)+1+j*(difference j n).2 := by
  induction n with
  | zero => simp [lucas,difference]
  | succ n ih =>
    rcases ih with ⟨h₀,h₁⟩
    simp only [lucas,difference,Int.natCast_succ]
    constructor <;> grobner

/-- This identity represents the quotient even when j is a zero divisor
    after reduction modulo the group order. -/
theorem integral_lucas_quotient (j : Nat) :
    (lucas ((j:Int)+2) j).1 = (j:Int)*(1+(difference j j).1) := by
  have h := (lucas_divided (j:Int) j).1
  grobner

set_option exponentiation.threshold 2400 in
theorem binary_anchor :
    2*3^1474 > (2:Nat)^2337+2 ∧ 4674*(2*3^1474-3) > (10:Nat)^707 := by decide

end ZeroInput

#print axioms ZeroInput.marked_product
#print axioms ZeroInput.translated_product
#print axioms ZeroInput.quadratic_row
#print axioms ZeroInput.nonzero_row_iff
#print axioms ZeroInput.projection_union
#print axioms ZeroInput.lucas_norm
#print axioms ZeroInput.lucas_divided
#print axioms ZeroInput.integral_lucas_quotient
#print axioms ZeroInput.binary_anchor
