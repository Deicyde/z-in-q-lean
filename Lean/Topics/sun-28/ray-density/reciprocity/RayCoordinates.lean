import IdealClasses
import PrimaryUnits
import CyclotomicCharacter
import Mathlib.Algebra.Group.Pi.Units

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin
noncomputable section
variable {I:Type*} (q:I→ℕ)

def levels : Option I→ℕ
  | none => 16
  | some i => q i

instance [∀i,NeZero (q i)] (j:Option I) : NeZero (levels q j) := by
  cases j with
  | none => exact inferInstanceAs (NeZero 16)
  | some i => exact inferInstanceAs (NeZero (q i))

abbrev M := modulus (levels q)
variable [Fintype I] [∀i,NeZero (q i)]

def crtUnits (cop:Pairwise (Function.onFun Nat.Coprime (levels q))) :
    (GaussianInt ⧸ M q)ˣ ≃* ((j:Option I)→GU (levels q j)) :=
  (Units.mapEquiv (gaussianCRT (levels q) cop).toMulEquiv).trans MulEquiv.piUnits

@[simp] theorem crtUnits_global (cop:Pairwise (Function.onFun Nat.Coprime (levels q)))
    (u:GaussianIntˣ) (j:Option I) :
    crtUnits q cop (unitReduction (M q) u) j = reducedUnit (levels q j) u := rfl

variable [∀i,Fact (q i).Prime]

def tupleRep : RayUnits q →* ((j:Option I)→GU (levels q j)) where
  toFun x j := match j with
    | none => primaryUnit x.1
    | some i => x.2 i
  map_one' := by funext j; cases j; exact map_one _; rfl
  map_mul' x y := by funext j; cases j; exact map_mul _ _ _; rfl

def rayWord (cop:Pairwise (Function.onFun Nat.Coprime (levels q))) :
    RayUnits q →* unitClasses (M q) :=
  (QuotientGroup.mk' _).comp ((crtUnits q cop).symm.toMonoidHom.comp (tupleRep q))

theorem rayWord_injective (cop:Pairwise (Function.onFun Nat.Coprime (levels q))) :
    Function.Injective (rayWord q cop) := by
  intro x y h
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨_,⟨u,rfl⟩,e⟩:=h
  have mapped:=congrArg (crtUnits q cop) e
  change crtUnits q cop ((crtUnits q cop).symm (tupleRep q x) * unitReduction (M q) u) =
    crtUnits q cop ((crtUnits q cop).symm (tupleRep q y)) at mapped
  rw [map_mul,MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply] at mapped
  have dy : primaryUnit x.1 * reducedUnit 16 u=primaryUnit y.1 := congrFun mapped none
  have trivial : u=1 := unit_trivial_on_primary (primaryUnit x.1) u x.1.2 (by rw [dy];exact y.1.2)
  subst u
  have pd : x.1=y.1 := Subtype.ext (by
    simpa using congrArg coords dy)
  refine Prod.ext pd (funext (fun i=>?_))
  have hj : x.2 i * reducedUnit (q i) 1=y.2 i := congrFun mapped (some i)
  simpa using hj

theorem rayWord_surjective (cop:Pairwise (Function.onFun Nat.Coprime (levels q))) :
    Function.Surjective (rayWord q cop) := by
  intro c
  obtain ⟨v,rfl⟩:=QuotientGroup.mk'_surjective (unitReduction (M q)).range c
  let t:=crtUnits q cop v
  obtain ⟨j,h⟩:=normalized_unit (t none)
  let u:=quarter j
  let x:RayUnits q := (⟨coords ((show GU 16 from t none)*reducedUnit 16 u),h⟩,
    fun i=>(show GU (q i) from t (some i))*reducedUnit (q i) u)
  refine ⟨x,Eq.symm ?_⟩
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨_,⟨u,rfl⟩,?_⟩
  apply (crtUnits q cop).injective
  change crtUnits q cop (v*unitReduction (M q) u)=crtUnits q cop ((crtUnits q cop).symm (tupleRep q x))
  rw [map_mul,MulEquiv.apply_symm_apply]
  funext i
  cases i with
  | none => apply Units.ext; apply QuadraticAlgebra.ext <;> rfl
  | some => rfl

def wordEquiv (cop:Pairwise (Function.onFun Nat.Coprime (levels q))) :
    RayUnits q ≃* unitClasses (M q) :=
  MulEquiv.ofBijective _ ⟨rayWord_injective q cop,rayWord_surjective q cop⟩

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.crtUnits_global
#print axioms Sun28.Reciprocity.rayWord_injective
#print axioms Sun28.Reciprocity.rayWord_surjective
#print axioms Sun28.Reciprocity.wordEquiv
