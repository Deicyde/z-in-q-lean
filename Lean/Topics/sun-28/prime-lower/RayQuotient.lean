import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Sun28.PrimeLower
open QuotientGroup
variable {U A B : Type*} [CommGroup U] [CommGroup A] [CommGroup B]
variable (a : U →* A) (b : U →* B)

/-- Diagonal Gaussian global-unit identifications in the finite CRT ring. -/
def diagonalUnit : U →* A × B := a.prod b

/-- Given a fixed base representative r, every ray class over it has a unique
representative (r,y). Faithfulness is checked at the base modulus only. -/
theorem unique_lift (faith : Function.Injective a) {r x : A} (v : B)
    (ray : (QuotientGroup.mk' a.range) r = (QuotientGroup.mk' a.range) x) :
    ∃! y : B, (QuotientGroup.mk' (diagonalUnit a b).range) (r,y) =
      (QuotientGroup.mk' (diagonalUnit a b).range) (x,v) := by
  obtain ⟨_,⟨u,rfl⟩,base⟩ := (QuotientGroup.mk'_eq_mk' a.range).mp ray
  refine ⟨v / b u,?_,?_⟩
  · apply (QuotientGroup.mk'_eq_mk' (diagonalUnit a b).range).mpr
    refine ⟨diagonalUnit a b u,⟨u,rfl⟩,Prod.ext base ?_⟩
    change (v / b u) * b u = v
    exact div_mul_cancel _ _
  · intro y h
    obtain ⟨_,⟨w,rfl⟩,eq⟩ := (QuotientGroup.mk'_eq_mk' (diagonalUnit a b).range).mp h
    have xw : r*a w=x := congrArg Prod.fst eq
    have uw := faith (mul_left_cancel (xw.trans base.symm))
    have byv : y*b w=v := congrArg Prod.snd eq
    rw [← byv, uw]
    exact (mul_div_cancel_right _ _).symm

end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.unique_lift
