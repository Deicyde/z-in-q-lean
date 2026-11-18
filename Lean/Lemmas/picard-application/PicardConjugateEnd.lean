import PicardDescent
import PrymFactor
import WittAscent
import QuadraticAction
import Mathlib.CategoryTheory.Conj
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.FieldTheory.Normal.Defs

/-!
# Endomorphism-compatible quasi-isogenies between conjugate Picard Jacobians

A rational endomorphism algebra identified with the full division quaternion
algebra is the geometric input. Coefficient conjugation, the corrected maps in
rationalized Hom, their inverses, and the intertwining of every endomorphism
are then assertions about the actual Picard group schemes.
-/

open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.AbelianModel ZInQBlueprint.NormalDescent
open scoped TensorProduct ZInQBlueprint.NormalDescent
namespace ZOverQ.Qualitative.PicardConjugateEnd
open PicardConjugation PicardDescent ZInQ
noncomputable section

section RationalHom
variable {C : Type*} [Category* C] [Preadditive C] {X Y Z T : C}

/-- Morphisms in the category up to isogeny. -/
abbrev QHom (X Y : C) := ℚ ⊗[ℤ] (X ⟶ Y)
abbrev QEnd (X : C) := ℚ ⊗[ℤ] End X

private def intComp (X Y Z : C) : (X ⟶ Y) →ₗ[ℤ] (Y ⟶ Z) →ₗ[ℤ] (X ⟶ Z) :=
  LinearMap.mk₂ ℤ (fun f g => f ≫ g) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp)

/-- Composition is obtained from ordinary composition by extension of scalars. -/
def comp {X Y Z : C} : QHom X Y →ₗ[ℚ] QHom Y Z →ₗ[ℚ] QHom X Z :=
  LinearMap.liftBaseChange ℚ ((LinearMap.baseChangeHom ℤ ℚ (Y ⟶ Z) (X ⟶ Z)).comp (intComp X Y Z))

@[simp] theorem comp_tmul (a b : ℚ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp (a ⊗ₜ[ℤ] f) (b ⊗ₜ[ℤ] g) = (a*b) ⊗ₜ[ℤ] (f ≫ g) := by
  simp [comp,intComp,TensorProduct.smul_tmul',smul_eq_mul]

private theorem assoc (x : QHom X Y) (y : QHom Y Z) (z : QHom Z T) :
    comp (comp x y) z = comp x (comp y z) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a f =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
    | tmul b g =>
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ h₁ h₂ => simp only [map_add,h₁,h₂]
      | tmul c h => simp [mul_assoc]

/-- Regard a rational endomorphism as a morphism in rationalized Hom. -/
def asHom (X : C) : QEnd X ≃ₗ[ℚ] QHom X X :=
  (End.linearEquiv (R:=ℤ) (X:=X)).baseChange ℤ ℚ _ _

@[simp] theorem asHom_tmul (a : ℚ) (f : End X) :
    asHom X (a ⊗ₜ[ℤ] f) = a ⊗ₜ[ℤ] f.asHom := by rfl

@[simp] theorem asHom_one : asHom X 1 = (1:ℚ) ⊗ₜ[ℤ] (𝟙 X) := rfl

private theorem end_comp (x y : QEnd X) :
    comp (asHom X x) (asHom X y) = asHom X (y*x) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,mul_add,h₁,h₂]
  | tmul a f =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add,add_mul,h₁,h₂]
    | tmul b g => simp [Algebra.TensorProduct.tmul_mul_tmul,mul_comm a b]

private def conjugateIntegral (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := fun f g => by
      apply End.ext
      change e.inv ≫ (f.asHom+g.asHom) ≫ e.hom =
        (e.inv ≫ f.asHom ≫ e.hom) + (e.inv ≫ g.asHom ≫ e.hom)
      simp }

private def intAlgConj (e : X ≅ Y) : End X ≃ₐ[ℤ] End Y where
  __ := conjugateIntegral e
  commutes' n := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    change (conjugateIntegral e) (n • (1 : End X)) = n • (1 : End Y)
    rw [map_zsmul,map_one]

def conjugateEnd (e : X ≅ Y) : QEnd X ≃ₐ[ℚ] QEnd Y :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) (intAlgConj e)

private theorem conj_commutes (e : X ≅ Y) (x : QEnd X) :
    comp (asHom X x) ((1:ℚ) ⊗ₜ[ℤ] e.hom) =
      comp ((1:ℚ) ⊗ₜ[ℤ] e.hom) (asHom Y (conjugateEnd e x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx,hy]
  | tmul a f =>
    change comp (asHom X (a ⊗ₜ[ℤ] f)) _ = comp _ (asHom Y (a ⊗ₜ[ℤ] e.conj f))
    simp

private theorem id_left (x : QHom X Y) :
    comp ((1:ℚ) ⊗ₜ[ℤ] (𝟙 X)) x = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx,hy]
  | tmul a f => simp

private theorem id_right (x : QHom X Y) :
    comp x ((1:ℚ) ⊗ₜ[ℤ] (𝟙 Y)) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx,hy]
  | tmul a f => simp

/-- A unit correcting the endomorphism action gives an actual invertible
element of rationalized Hom, intertwining the entire coefficient action. -/
theorem corrected_map (e : X ≅ Y) (F : QEnd Y →ₐ[ℚ] QEnd X) (w : (QEnd Y)ˣ)
    (correct : ∀ z : QEnd Y, (w:QEnd Y)*conjugateEnd e (F z) = z*(w:QEnd Y)) :
    ∃ (μ : QHom X Y) (ν : QHom Y X),
      comp μ ν = (1:ℚ) ⊗ₜ[ℤ] 𝟙 X ∧ comp ν μ = (1:ℚ) ⊗ₜ[ℤ] 𝟙 Y ∧
      ∀ z : QEnd Y, comp (asHom X (F z)) μ = comp μ (asHom Y z) := by
  let a : QHom X Y := (1:ℚ) ⊗ₜ[ℤ] e.hom
  let b : QHom Y X := (1:ℚ) ⊗ₜ[ℤ] e.inv
  let W := asHom Y (w:QEnd Y)
  let V := asHom Y (↑w⁻¹:QEnd Y)
  have ab : comp a b = (1:ℚ) ⊗ₜ[ℤ] 𝟙 X := by simp [a,b]
  have ba : comp b a = (1:ℚ) ⊗ₜ[ℤ] 𝟙 Y := by simp [a,b]
  have wv : comp W V = (1:ℚ) ⊗ₜ[ℤ] 𝟙 Y := by simp [W,V,end_comp]
  have vw : comp V W = (1:ℚ) ⊗ₜ[ℤ] 𝟙 Y := by simp [W,V,end_comp]
  refine ⟨comp a W,comp V b,?_,?_,?_⟩
  · rw [assoc,← assoc W V b,wv,id_left,ab]
  · rw [assoc,← assoc b a W,ba,id_left,vw]
  · intro z
    rw [← assoc,conj_commutes,assoc,assoc,end_comp,end_comp,correct]

end RationalHom

/-- The actual action of scalar extension on the rational endomorphism algebra. -/
private def intAlgChange {K L : Type} [Field K] [Field L] (φ : K →+* L) (J : GroupScheme K) :
    End J →ₐ[ℤ] End ((baseChange φ).obj J) where
  __ := changeEndRing (Over.pullback (Spec.map (CommRingCat.ofHom φ))) J
  commutes' n := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    change (changeEndRing (Over.pullback (Spec.map (CommRingCat.ofHom φ))) J) (n • (1:End J)) = n • 1
    rw [map_zsmul,map_one]

def change {K L : Type} [Field K] [Field L] (φ : K →+* L) (J : GroupScheme K) :
    QEnd J →ₐ[ℚ] QEnd ((baseChange φ).obj J) :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (intAlgChange φ J)

/-- The actual twisted Jacobian after extension to the field of definition
of all its quaternionic endomorphisms. -/
def familyOver {L : Type} [Field L] [CharZero L] (ψ : fixedField →ₐ[ℚ] L)
    (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0) : GroupScheme L :=
  (baseChange ψ.toRingHom).obj (familyJacobian t d ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField))

/-- Every conjugate is isomorphic over a field containing the chart coefficients. -/
theorem conjugate_family {L : Type} [Field L] [CharZero L] (ψ : fixedField →ₐ[ℚ] L)
    (σ : L ≃ₐ[ℚ] L) (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0) :
    Nonempty ((baseChange σ.toRingHom).obj (familyOver ψ t d ht hd) ≅ familyOver ψ t d ht hd) := by
  let J := familyJacobian t d ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
  let := ψ.toAlgebra
  let : IsScalarTower ℚ fixedField L := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  let τ := σ.restrictNormal fixedField
  have h : σ.toRingHom.comp ψ.toRingHom = ψ.toRingHom.comp τ.toRingHom :=
    RingHom.ext fun x => (σ.restrictNormal_commutes fixedField x).symm
  obtain ⟨f⟩ := family_galois_pullback t d ht hd τ
  exact ⟨(WittAscent.baseChangeCompIso ψ.toRingHom σ.toRingHom J).symm ≪≫
    eqToIso (congrArg (fun h : fixedField →+* L => (baseChange h).obj J) h) ≪≫
    WittAscent.baseChangeCompIso τ.toRingHom ψ.toRingHom J ≪≫ (baseChange ψ.toRingHom).mapIso f⟩

/-- Full quaternionic multiplication over L supplies an invertible rational
endomorphism-compatible homomorphism for every Galois conjugate of the
actual twisted Jacobian. The single geometric premise identifies its full
endomorphism algebra over L with the stated quaternion algebra. -/
theorem family_quasi_isogeny {L D : Type} [Field L] [CharZero L] [DivisionRing D] [Algebra ℚ D]
    (ψ : fixedField →ₐ[ℚ] L) (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0)
    (str : D ≃ₐ[ℚ] QEnd (familyOver ψ t d ht hd))
    (i j : D) (hi : i*i = algebraMap ℚ D (-3)) (hj : j*j = algebraMap ℚ D 2)
    (skew : j*i = -(i*j)) (gen : Algebra.adjoin ℚ ({i,j} : Set D) = ⊤) (σ : L ≃ₐ[ℚ] L) :
    let Y := familyOver ψ t d ht hd
    let X := (baseChange σ.toRingHom).obj Y
    ∃ (μ : QHom X Y) (ν : QHom Y X),
      comp μ ν = (1:ℚ) ⊗ₜ[ℤ] 𝟙 X ∧ comp ν μ = (1:ℚ) ⊗ₜ[ℤ] 𝟙 Y ∧
      ∀ z : QEnd Y, comp (asHom X (change σ.toRingHom Y z)) μ = comp μ (asHom Y z) := by
  let Y := familyOver ψ t d ht hd
  let F := change σ.toRingHom Y
  obtain ⟨e⟩ := conjugate_family ψ σ t d ht hd
  let rep := (conjugateEnd e).toAlgHom.comp F
  let h := str.symm.toAlgHom.comp (rep.comp str.toAlgHom)
  have ni : i ≠ 0 := by
    intro e
    have n := (algebraMap ℚ D).injective.ne (show (-3:ℚ) ≠ 0 by norm_num)
    apply n
    simpa [e] using hi.symm
  have nj : j ≠ 0 := by
    intro e
    have n := (algebraMap ℚ D).injective.ne (show (2:ℚ) ≠ 0 by norm_num)
    apply n
    simpa [e] using hj.symm
  obtain ⟨w,hw⟩ := Prym.intertwine_algebra h (AlgHom.id ℚ D) i j (-3) 2 ni nj hi hj skew gen
  let W : (QEnd Y)ˣ := Units.map str.toMonoidHom w
  apply corrected_map e F W
  intro z
  have step (x : D) : str (h x) = conjugateEnd e (F (str x)) := str.apply_symm_apply _
  have hz := congrArg (fun u : D => str u) (hw (str.symm z))
  simp only [map_mul,step,AlgHom.id_apply,str.apply_symm_apply] at hz
  exact hz

end
end ZOverQ.Qualitative.PicardConjugateEnd

#print axioms ZOverQ.Qualitative.PicardConjugateEnd.corrected_map
#print axioms ZOverQ.Qualitative.PicardConjugateEnd.conjugate_family
#print axioms ZOverQ.Qualitative.PicardConjugateEnd.family_quasi_isogeny
