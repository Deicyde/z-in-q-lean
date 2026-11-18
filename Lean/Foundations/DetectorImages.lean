module

public import Std

@[expose] public section

namespace DetectorImages
open Lean.Grind

/-- Preserve the first quadratic factor under the addition law of the norm torus. -/
theorem pencil_factor {R : Type} [CommRing R] (β x l : R) :
    (1+β*l*x)^2-β*(x+l)^2=(1-β*x^2)*(1-β*l^2) := by grobner

/-- An odd ramification index preserves the odd order of the detector target. -/
theorem local_odd (a k n : Int) : (2*a+1)*(-16*k-1) ≠ 2*n := by
  have h : (2*a+1)*(-16*k-1) = 2*(-16*a*k-a-8*k-1)+1 := by grobner
  omega

/-- Opposite parities force the minimum of the two valuations to survive. -/
theorem opposite_orders (a b : Int) : 2*a ≠ 2*b+1 := by omega

def firstProduct (t : Fin 149) : Fin 149 :=
  let y := 51*t*t+2504
  let r := y*(y-1)*(y-2401)*(32*y+343)*(2*y-1)
  r*(r+4896)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem no_root_149 : ∀ t : Fin 149, firstProduct t ≠ 0 := by decide

theorem square_root_orders (a b d k : Int)
    (hs : a+b=2+2*k) (hd : a+b<d)
    (hn : a≠b → d=min (2*a) (2*b)) : a=1+k ∧ b=1+k := by
  by_cases h : a=b
  · omega
  · have hh := hn h
    omega

theorem joint_orders (w x y z k : Nat) :
    (0 ≤ -(2:Int)*((w:Int)+x+y+z) ∧ (1475:Int) ≤ 1+(k:Int)) ↔
      (w=0 ∧ x=0 ∧ y=0 ∧ z=0 ∧ (2949:Int) ≤ 2+2*(k:Int)) := by
  omega

#print axioms square_root_orders
#print axioms joint_orders
#print axioms pencil_factor
#print axioms local_odd
#print axioms opposite_orders
#print axioms no_root_149
end DetectorImages
