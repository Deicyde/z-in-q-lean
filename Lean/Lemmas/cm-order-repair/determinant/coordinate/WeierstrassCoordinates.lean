import VoightFiniteCoordinates
import SixPolarizedIgusa

/-! The change of Weierstrass coordinates on the two standard charts of any
separable binary sextic over the algebraic closure of the rationals. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeierstrassCoordinates
open BinaryCover WeightedCurvePoints MarkedForm GeometricMarking NormalDescent
open SexticIgusaChart
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The finite point of the doubled line obtained from the two coordinates
of a square root of the dehomogenized form. -/
def chartCoordinates (f : Qbar[X]) (F : Qbar × Qbar → Qbar)
    (h : ∀ x : Qbar, aeval x f = F (x,1)) (p : Finite F) : AffineCoords Qbar f :=
  ⟨p.1, p.2.trans (h p.1.1).symm⟩

def finiteReader (f g : Qbar[X]) (overlap : SexticOverlap Qbar f g)
    (F : Qbar × Qbar → Qbar) (eval : ∀ x : Qbar, aeval x f = F (x,1))
    (p : Finite F) : Sections Qbar (gluedOver Qbar f g overlap) :=
  chartSection f g overlap false (chartCoordinates f F eval p)

/-- Only the affine chart on which the transformed point is finite
enters the formula. -/
def HasFiniteAction (C : Over (Spec (.of Qbar))) (F : Qbar × Qbar → Qbar)
    (read : Finite F → Sections Qbar C) : Prop :=
  ∀ e : C ≅ C, ∃ (m : (Qbar × Qbar) ≃ₗ[Qbar] (Qbar × Qbar)) (k : Qbarˣ),
    (∀ v, F (m v) = (k : Qbar)^2 * F v) ∧
    ∀ p : Finite F, (m (p.1.1,1)).2 ≠ 0 → ∃ q : Finite F,
      read p ≫ e.hom = read q ∧
      q.1.1 = (m (p.1.1,1)).1 / (m (p.1.1,1)).2 ∧
      q.1.2 = (k : Qbar) * p.1.2 / (m (p.1.1,1)).2^3

/-- Voight (43.3.3) on the standard projective completion of a separable
degree-six Weierstrass equation. The Laurent identity in `overlap` is
f(1/t) = g(t)/t⁶. The binary form is homogeneous by its coefficient vector. -/
def VoightCoordinateFormula : Prop :=
  ∀ (f g : Qbar[X]) (overlap : SexticOverlap Qbar f g)
    (b : Coeff Qbar 6) (F : Qbar × Qbar → Qbar),
    f.natDegree = 6 → f.Separable → (∀ p, evalF b p.1 p.2 = F p) →
    ∀ eval : (∀ x : Qbar, aeval x f = F (x,1)),
    HasFiniteAction (gluedOver Qbar f g overlap) F (finiteReader f g overlap F eval)

private theorem conjugate_section {D : Type*} [Category D] {S C C' : D}
    (i : C ≅ C') (e : C' ≅ C') (p q : S ⟶ C)
    (h : p ≫ (i ≪≫ e ≪≫ i.symm).hom = q) :
    (p ≫ i.hom) ≫ e.hom = q ≫ i.hom := by
  rw [← h]
  simp

/-- Transport the finite-coordinate formula along any isomorphism of
models. This proof also allows a point map already defined on the new model. -/
theorem finiteAction_of_iso {C D : Over (Spec (.of Qbar))} (i : C ≅ D)
    (F : Qbar × Qbar → Qbar) (r : Finite F → Sections Qbar C) (s : Finite F → Sections Qbar D)
    (h : ∀ p, s p = r p ≫ i.hom) (act : HasFiniteAction C F r) : HasFiniteAction D F s := by
  intro e
  obtain ⟨m,k,hm,hp⟩ := act (i ≪≫ e ≪≫ i.symm)
  refine ⟨m,k,hm,fun p hd => ?_⟩
  obtain ⟨q,he,hx,hy⟩ := hp p hd
  refine ⟨q,?_,hx,hy⟩
  rw [h p,h q]
  exact conjugate_section i e (r p) (r q) he

end
end ZInQBlueprint.WeierstrassCoordinates
#print axioms ZInQBlueprint.WeierstrassCoordinates.finiteAction_of_iso
