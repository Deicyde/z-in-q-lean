import GaloisComparison
import PrintedJacobian

/-! Marked field of moduli on the printed model and its consequence for
the signed rational Jacobian. The central automorphism is the quotient
of two isomorphisms to the same conjugate polarized surface. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.QuaternionMarking
open AbelianModel NormalDescent GeometricMarking
open scoped NormalDescent CategoryTheory.MonObj
noncomputable section
variable {u : ℚ} {hu : u ∉ ZInQ.contactSet}
local notation "J" => geometricJacobian hu
local notation "A" => SixJacobian.jacobian hu
variable {P : GroupScheme Qbar}
private abbrev pull (σ : Qbar ≃ₐ[ℚ] Qbar) := (conjugation σ.toRingEquiv).mapCommGrp
private abbrev underlying {X Y : GroupScheme Qbar} (f : X ⟶ Y) := f.hom.hom.hom.left

/-- A comparison of the printed polarized variety with its conjugate, obtained
from the defining integral model over Q by change of coordinates. -/
def rationalOnPrinted (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar) : P ≅ (pull σ).obj P :=
  e.symm ≪≫ rationalGroupComparison A σ ≪≫ (pull σ).mapIso e

/-- The difference of two marked comparison maps on P is a group automorphism. -/
def correctionIso (e : J ≅ P) (σ : Qbar ≃ₐ[ℚ] Qbar) (φ : P ≅ (pull σ).obj P) : J ≅ J :=
  e ≪≫ φ ≪≫ (rationalOnPrinted e σ).symm ≪≫ e.symm

/-- Naturality of the first projection on the conjugate scheme. -/
theorem pull_fst {X Y : GroupScheme Qbar} (σ : Qbar ≃ₐ[ℚ] Qbar) (f : X ⟶ Y) :
    underlying ((pull σ).map f) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ underlying f :=
  pullback.lift_fst ..

private abbrev projection (σ : Qbar ≃ₐ[ℚ] Qbar) (B : GroupScheme Qbar) :
    ((pull σ).obj B).X.left ⟶ B.X.left := pullback.fst _ _

private theorem projected_square {X Y : Scheme} (e a d : X ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Y)
    (π : Y ⟶ X) (prod : f ≫ π = a ≫ d) (nat : g ≫ π = π ≫ e) (sq : e ≫ f = f ≫ g) :
    (a ≫ d) ≫ e = e ≫ a ≫ d := by
  rw [← prod, Category.assoc, ← nat, ← Category.assoc, ← sq, Category.assoc]

private theorem switch_correction {X : Scheme} (e a b d : X ⟶ X)
    (ba : b ≫ a = 𝟙 X) (commute : e ≫ a = a ≫ e)
    (h : (a ≫ d) ≫ e = e ≫ a ≫ d) : (d ≫ a) ≫ e = e ≫ d ≫ a := by
  have plain : d ≫ e = e ≫ d := by
    calc d ≫ e = (b ≫ a) ≫ d ≫ e := by rw [ba,Category.id_comp]
         _ = b ≫ (a ≫ d) ≫ e := by simp only [Category.assoc]
         _ = b ≫ e ≫ a ≫ d := by rw [h]
         _ = b ≫ (e ≫ a) ≫ d := by simp only [Category.assoc]
         _ = e ≫ d := by rw [commute]; simp only [← Category.assoc,ba,Category.id_comp]
  rw [Category.assoc,← commute,← Category.assoc,plain,Category.assoc]

/-- If φ respects the marked element, its discrepancy with rational descent
commutes with that element after the semilinear comparison. -/
theorem corrected_generator (e : J ≅ P) (act : LevelThree.O →+* End P)
    (σ : Qbar ≃ₐ[ℚ] Qbar) (φ : P ≅ (pull σ).obj P)
    (hφ : (act sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (pull σ).map (act sqrtThree).asHom) :
    let E := underlying (restrictedAction e act QuadraticAlgebra.omega).asHom
    let a := underlying (correctionIso e σ φ).hom
    (a ≫ deck (SixJacobian.jacobian hu).X.hom σ) ≫ E = E ≫ a ≫ deck (SixJacobian.jacobian hu).X.hom σ := by
  let E := (restrictedAction e act QuadraticAlgebra.omega).asHom
  let ψ := e ≪≫ φ ≪≫ (pull σ).mapIso e.symm
  let c := rationalGroupComparison A σ
  let a := correctionIso e σ φ
  have fac : a.hom ≫ c.hom = ψ.hom := by
    dsimp [a, correctionIso, rationalOnPrinted, ψ, c]
    simp
  have eq : E ≫ ψ.hom = ψ.hom ≫ (pull σ).map E := transport_intertwiner e act σ.toRingEquiv φ hφ
  let π := projection σ J
  let d : (geometricJacobian hu).X.left ⟶ (geometricJacobian hu).X.left := deck (SixJacobian.jacobian hu).X.hom σ
  have first : underlying c.hom ≫ π = d := comparison_fst A σ
  have prod : underlying ψ.hom ≫ π = underlying a.hom ≫ d := by
    rw [← fac]
    exact (Category.assoc (underlying a.hom) (underlying c.hom) π).trans
      (congrArg (fun k => underlying a.hom ≫ k) first)
  exact projected_square (underlying E) (underlying a.hom) d (underlying ψ.hom)
    (underlying ((pull σ).map E)) π prod (pull_fst σ E) (congrArg underlying eq)

/-- Reordering a signed correction is unnecessary for descent. Both signs
are group automorphisms and commute with every group endomorphism. -/
def marked_of_printed (D : DivisorData hu) (preserves : (J ≅ J) → Prop)
    (T : PolarizedTorelli D preserves) (e : J ≅ P) (act : LevelThree.O →+* End P)
    (hact : Function.Injective act)
    (moduli : IsSquare (-(27*SixContact.J u+16)/SixContact.J u) →
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∃ φ : P ≅ (pull σ).obj P,
        (act sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (pull σ).map (act sqrtThree).asHom ∧
        preserves (correctionIso e σ φ)) :
    JacobianHeight.MarkedAction u A := by
  let i := restrictedAction e act
  let E := (i QuadraticAlgebra.omega).asHom
  apply markedAction_of_divisors D preserves T i (restricted_faithful e hact)
  intro square
  dsimp only
  intro σ
  obtain ⟨φ,ht,hp⟩ := moduli square σ
  let a := correctionIso e σ φ
  have h := corrected_generator e act σ φ ht
  have signs := polarized_signs D.comparison (torelli_on_points D T) (groupMap a) ⟨a,hp,rfl⟩
  change (groupMap a ≫ deck (SixJacobian.jacobian hu).X.hom σ) ≫ underlying E = underlying E ≫ groupMap a ≫ deck (SixJacobian.jacobian hu).X.hom σ at h
  have commute : underlying E ≫ groupMap a = groupMap a ≫ underlying E := by
    rcases signs with hs|hs
    · simp [hs]
    · rw [hs]
      exact congrArg Over.Hom.left (GrpObj.inv_hom E.hom.hom.hom).symm
  refine ⟨groupMap a, ⟨a,hp,rfl⟩, ?_⟩
  exact switch_correction (underlying E) (groupMap a) (underlying a.inv)
    (show (geometricJacobian hu).X.left ⟶ (geometricJacobian hu).X.left from deck (SixJacobian.jacobian hu).X.hom σ)
    (congrArg underlying a.inv_hom_id) commute h

end
end ZInQBlueprint.QuaternionMarking
#print axioms ZInQBlueprint.QuaternionMarking.corrected_generator
#print axioms ZInQBlueprint.QuaternionMarking.marked_of_printed
