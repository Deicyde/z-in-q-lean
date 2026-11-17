import QuadraticContact

namespace IndependentIndices.Examples
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- At m=2 the second multiplier vanishes; the arithmetic still recovers the labels. -/
private def indexTwo (R : Type) [CommRing R] (n : Int) : LogRow R 2 n where
  u := n
  primary := (n:R)
  alternate := (n:R)
  cross := rfl
  primaryLog := by have eq : ((2:Int):R)=(2:R) := Ring.intCast_ofNat 2;rw [eq]
  alternateLog := by have eq : ((2:Int):R)=(2:R) := Ring.intCast_ofNat 2;rw [eq];grobner

private def labels : Labels := ⟨29526,7,1+(3:Int)^40,0⟩
private def beta : Rat := ⟨3,2,by decide,by decide⟩

private def actualRows : Ratios (Fin (3^10)) (Fin (3^40)) 2 labels beta where
  first := indexTwo _ _
  second := indexTwo _ _
  third := indexTwo _ _
  fourth := indexTwo _ _
  detector := by decide
  lucasTest := by decide

theorem nonzero_numerator : Defects 3 labels beta ∧ ((labels.n₁:Rat)-beta).num=59049 ∧ beta.den.Coprime (3^10) := by
  have h:=finite_place 3 (by decide) actualRows
  exact ⟨h.1,by rw [reduced_num];rfl,h.2⟩

theorem overlapping_empty :
    radical ([3,5]++([] : List Nat)++[5,7])=105 ∧
    largest (radical [3,5]) (radical []) (radical [5,7])=35 := by decide

theorem nonintegral_index : halfIndex (R:=Fin 27) 27 1=14 ∧ halfIndex (R:=Fin 27) 27 (-1)=13 := by decide

end IndependentIndices.Examples
