import IteratedResultant
import Mathlib.Data.Multiset.Bind

/-! The product formula for iterated resultants records the actual root multiplicities. -/
open Polynomial
namespace ZInQBlueprint.SunResultant.ParamTower
noncomputable section
variable {R L : Type*} [CommRing R] [Field L]

/-- Geometric tuples, repeated with the product of their one-step root multiplicities. -/
def rootTuples (φ : R →+* L) : {n : ℕ} → ParamTower R n → Multiset (Fin n → L)
  | _, .base => {Fin.elim0}
  | _, .adjoin T f _ => (rootTuples φ T).bind fun x =>
      (f.map (MvPolynomial.eval₂Hom φ x)).roots.map (fun a => Fin.cons a x)

/-- Uniform multiplicity budget of the full tower. -/
def degreeProduct : {n : ℕ} → ParamTower R n → ℕ
  | _, .base => 1
  | _, .adjoin T f _ => degreeProduct T * f.natDegree

theorem card_rootTuples [IsAlgClosed L] (φ : R →+* L) {n : ℕ} (T : ParamTower R n) :
    (rootTuples φ T).card = T.degreeProduct := by
  induction T with
  | base => simp [rootTuples,degreeProduct]
  | @adjoin n T f hf ih =>
    rw [rootTuples,degreeProduct,Multiset.card_bind]
    have each (x : Fin n → L) :
        ((f.map (MvPolynomial.eval₂Hom φ x)).roots.map (fun a : L => (Fin.cons a x : Fin (n+1) → L))).card = f.natDegree := by
      rw [Multiset.card_map,← (IsAlgClosed.splits _).natDegree_eq_card_roots,hf.natDegree_map]
    simp only [Function.comp_apply,each,Multiset.map_const',Multiset.sum_replicate,smul_eq_mul,ih]

theorem mem_rootTuples (φ : R →+* L) {n : ℕ} (T : ParamTower R n) (x : Fin n → L) :
    x ∈ rootTuples φ T ↔ Satisfies φ T x := by
  induction T with
  | base =>
    simp only [rootTuples,Multiset.mem_singleton,Satisfies,iff_true]
    exact Subsingleton.elim _ _
  | @adjoin n T f hf ih =>
    simp only [rootTuples,Multiset.mem_bind,Multiset.mem_map,Satisfies]
    constructor
    · rintro ⟨y,hy,a,ha,rfl⟩
      simp only [Fin.tail_cons,Fin.cons_zero]
      exact ⟨(ih y).mp hy,(mem_roots (hf.map _).ne_zero).mp ha⟩
    · rintro ⟨hy,ha⟩
      exact ⟨Fin.tail x,(ih _).mpr hy,x 0,(mem_roots (hf.map _).ne_zero).mpr ha,Fin.cons_self_tail x⟩

/-- One concrete element of R specializes to the product over all tuples with precisely
the recursive multiplicity coming from the monic equations. -/
theorem elim_product [IsAlgClosed L] (φ : R →+* L) {n : ℕ} (T : ParamTower R n) (g : MvPolynomial (Fin n) R) :
    φ (elim T g) = ((rootTuples φ T).map (fun x => MvPolynomial.eval₂Hom φ x g)).prod := by
  induction T with
  | base =>
    simp only [elim,rootTuples,Multiset.map_singleton,Multiset.prod_singleton]
    have h : φ.comp (MvPolynomial.eval Fin.elim0) = MvPolynomial.eval₂Hom φ (fun i : Fin 0 => i.elim0) :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun i => i.elim0)
    exact DFunLike.congr_fun h g
  | @adjoin n T f hf ih =>
    rw [elim,ih,rootTuples,Multiset.map_bind,Multiset.prod_bind]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    rw [specialize_resultant _ _ _ hf,Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    exact (eval_cons φ x a g).symm

end
end ZInQBlueprint.SunResultant.ParamTower
#print axioms ZInQBlueprint.SunResultant.ParamTower.mem_rootTuples
#print axioms ZInQBlueprint.SunResultant.ParamTower.elim_product
#print axioms ZInQBlueprint.SunResultant.ParamTower.card_rootTuples
