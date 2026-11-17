import Mathlib.Tactic

namespace Sun28.SmallImage
namespace Ternary
private abbrev M := ZMod 27
private def squares : List M := [0,1,4,7,9,10,13,16,19,22,25]
private theorem sq_in (i : M) : i^2∈squares := by revert i; decide +kernel

/-- For fixed a,b, compute the possible pairs (b y², a z²) from x,t,
and check them against all allowed square residues. A normalized coordinate
must be one, so the corresponding square must also equal one. -/
private def certificate (a b : M) : Bool :=
  if a.val%9=0 ∨ b.val%9=0 ∨ (b.val%3=1) then true else
  squares.all (fun x=>squares.all (fun t=>
    let abx := a*b*x
    let byv := abx-11*t
    let azv := abx+6*t
    squares.all (fun y=> if b*y=byv then squares.all
      (fun z=>decide (a*z≠azv ∨ ¬(x=1 ∨ y=1 ∨ z=1 ∨ t=1))) else true)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem cert (a b : M) : certificate a b=true := by
  fin_cases a <;> revert b <;> decide +kernel

end Ternary
open _root_.Sun28.SmallImage.Ternary in
theorem ternary_table (a b x y z t : ZMod 27) (ha : a.val%9≠0) (hb : b.val%9≠0)
    (prim : x=1 ∨ y=1 ∨ z=1 ∨ t=1) (e : a*b*x^2-b*y^2=11*t^2)
    (f : a*z^2-a*b*x^2=6*t^2) : b.val%3=1 := by
  by_contra bad
  have C := cert a b
  have ne : ¬(a.val%9=0 ∨ b.val%9=0 ∨ (b.val%3=1)) := by tauto
  have E : b*y^2=a*b*x^2-11*t^2 := by linear_combination -e
  have F : a*z^2=a*b*x^2+6*t^2 := by linear_combination f
  simp only [certificate,eq_false ne,ite_false,List.all_eq_true] at C
  have R:=C _ (sq_in x) _ (sq_in t) _ (sq_in y)
  simp only [E,ite_true,List.all_eq_true,decide_eq_true_eq] at R
  rcases R _ (sq_in z) with H|H
  · exact H F
  · exact H (by rcases prim with h|h|h|h <;> simp [h])

end Sun28.SmallImage
#print axioms Sun28.SmallImage.ternary_table
