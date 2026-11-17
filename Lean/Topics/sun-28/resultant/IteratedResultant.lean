import SpecializedResultant
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Iterated resultants for monic triangular equations over an arbitrary parameter ring. -/
open Polynomial
namespace ZInQBlueprint.SunResultant
noncomputable section
universe u
inductive ParamTower (R : Type u) [CommRing R] : ℕ → Type u
  | base : ParamTower R 0
  | adjoin {n : ℕ} (prior : ParamTower R n) (f : Polynomial (MvPolynomial (Fin n) R))
      (hf : f.Monic) : ParamTower R (n+1)

namespace ParamTower
variable {R L : Type*} [CommRing R] [Field L]

/-- One nested resultant in the original coefficient ring, determined before specialization. -/
def elim : {n : ℕ} → ParamTower R n → MvPolynomial (Fin n) R → R
  | _, .base, g => MvPolynomial.eval Fin.elim0 g
  | _, .adjoin T f _, g => elim T (f.resultant (MvPolynomial.finSuccEquiv R _ g))

/-- Evaluation of the triangular equations after applying an arbitrary coefficient map. -/
def Satisfies (φ : R →+* L) : {n : ℕ} → ParamTower R n → (Fin n → L) → Prop
  | _, .base, _ => True
  | _, .adjoin T f _, x => Satisfies φ T (Fin.tail x) ∧
      (f.map (MvPolynomial.eval₂Hom φ (Fin.tail x))).IsRoot (x 0)

theorem eval_cons (φ : R →+* L) {n : ℕ} (x : Fin n → L) (a : L) (g : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial.eval₂Hom φ (Fin.cons a x) g =
      ((MvPolynomial.finSuccEquiv R n g).map (MvPolynomial.eval₂Hom φ x)).eval a := by
  let h := ((Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (MvPolynomial.eval₂Hom φ x))).comp
    (MvPolynomial.finSuccEquiv R n).toRingHom
  have he : MvPolynomial.eval₂Hom φ (Fin.cons a x) = h := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [h,MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [h,MvPolynomial.finSuccEquiv_apply]
  exact DFunLike.congr_fun he g

private theorem eval_empty (φ : R →+* L) (g : MvPolynomial (Fin 0) R) :
    φ (MvPolynomial.eval Fin.elim0 g) = MvPolynomial.eval₂Hom φ (fun i : Fin 0 => i.elim0) g := by
  have h : φ.comp (MvPolynomial.eval Fin.elim0) = MvPolynomial.eval₂Hom φ (fun i : Fin 0 => i.elim0) :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => i.elim0)
  exact DFunLike.congr_fun h g

/-- The same parameter polynomial describes the existence of a geometric tuple at *every*
specialization, including all drops in the degrees of successive test resultants. -/
theorem elim_zero_iff [IsAlgClosed L] (φ : R →+* L) {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) :
    φ (elim T g) = 0 ↔ ∃ x : Fin n → L, Satisfies φ T x ∧ MvPolynomial.eval₂Hom φ x g = 0 := by
  induction T with
  | base =>
    rw [elim,eval_empty]
    constructor
    · intro h; exact ⟨Fin.elim0,trivial,h⟩
    · rintro ⟨x,hx,hg⟩
      have eq : x = Fin.elim0 := Subsingleton.elim _ _
      exact eq ▸ hg
  | @adjoin n T f hf ih =>
    rw [elim,ih]
    constructor
    · rintro ⟨x,hx,h⟩
      obtain ⟨a,ha,hg⟩ := (specialize_resultant_zero_iff (MvPolynomial.eval₂Hom φ x) _ _ hf).mp h
      exact ⟨Fin.cons a x,⟨by simpa using hx,by simpa using ha⟩,by rw [eval_cons]; exact hg⟩
    · rintro ⟨x,⟨hx,ha⟩,hg⟩
      refine ⟨Fin.tail x,hx,(specialize_resultant_zero_iff (MvPolynomial.eval₂Hom φ (Fin.tail x)) _ _ hf).mpr
        ⟨x 0,ha,?_⟩⟩
      change ((MvPolynomial.finSuccEquiv R n g).map (MvPolynomial.eval₂Hom φ (Fin.tail x))).eval (x 0) = 0
      rw [← eval_cons,Fin.cons_self_tail]
      exact hg

end ParamTower
end
end ZInQBlueprint.SunResultant
#print axioms ZInQBlueprint.SunResultant.ParamTower.eval_cons
#print axioms ZInQBlueprint.SunResultant.ParamTower.elim_zero_iff
