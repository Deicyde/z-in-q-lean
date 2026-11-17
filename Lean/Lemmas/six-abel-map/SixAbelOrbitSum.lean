import SixAbelGeneration

/-! A principal difference of two orbit divisors gives equality of the sums
of the two corresponding Abel images, also for fixed and coinciding points. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.SixAbelMap
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
variable {C : Over (Spec (.of K))} {M : CurveModel K F} {i : M.C ≅ C.left}
  {hbase : i.hom ≫ C.hom=M.toBase} {V : AbelianModel.GroupScheme K} {b : base K ⟶ C}

def degreeTwo (P Q : Place K F) : Divisor K F := Finsupp.single P 1 + Finsupp.single Q 1

theorem AbelPresentation.sum_eq_of_principal (A : AbelPresentation C M i hbase V b)
    (p p' q q' : base K ⟶ C)
    (h : (degreeTwo (pointPlace C M i hbase p) (pointPlace C M i hbase p') -
      degreeTwo (pointPlace C M i hbase q) (pointPlace C M i hbase q')).IsPrincipal) :
    A.abel p + A.abel p' = A.abel q + A.abel q' := by
  let v := pointPlace C M i hbase
  let D := difference (v p) (v q) + difference (v p') (v q')
  have hd : (D : Divisor K F) = degreeTwo (v p) (v p') - degreeTwo (v q) (v q') := by
    change (_ - _ : Divisor K F) + (_ - _) = (_ + _) - (_ + _)
    abel
  have hp : Pic0.mk D = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (show (D : Divisor K F).IsPrincipal from hd ▸ h)
  have hv : A.abel p - A.abel q + (A.abel p' - A.abel q') = 0 := by
    rw [A.difference_class,A.difference_class,←map_add,←Pic0.mk_add]
    exact (congrArg A.divisorEquiv hp).trans A.divisorEquiv.map_zero
  calc
    A.abel p + A.abel p' = A.abel p - A.abel q + (A.abel p' - A.abel q') + (A.abel q+A.abel q') := by abel
    _ = A.abel q+A.abel q' := by rw [hv,zero_add]

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.AbelPresentation.sum_eq_of_principal
