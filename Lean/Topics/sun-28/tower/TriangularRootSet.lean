import RationalProjection
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Specialization of triangular equations without a separability or discriminant requirement. -/
open Polynomial Finset
namespace ZInQBlueprint.SunTower
noncomputable section
universe u
/-- Each new root is placed first in its tuple. Coefficients of the next monic equation
are polynomials over K in all preceding roots. -/
inductive Tower (K : Type u) [Field K] : ℕ → Type u
  | base : Tower K 0
  | adjoin {n : ℕ} (prior : Tower K n) (f : Polynomial (MvPolynomial (Fin n) K))
      (hf : f.Monic) : Tower K (n+1)

namespace Tower
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Product of the degrees written in the tower. -/
def degreeBound : {n : ℕ} → Tower K n → ℕ
  | _, .base => 1
  | _, .adjoin T f _ => degreeBound T * f.natDegree

/-- The equations after evaluating every earlier coordinate in L. -/
def Satisfies : {n : ℕ} → Tower K n → (Fin n → L) → Prop
  | _, .base, _ => True
  | _, .adjoin T f _, x => Satisfies T (Fin.tail x) ∧
      (f.map (MvPolynomial.aeval (R:=K) (Fin.tail x)).toRingHom).IsRoot (x 0)

/-- Distinct roots are taken at each step, even on a specialization with multiple roots. -/
def solutions (L : Type*) [Field L] [Algebra K L] : {n : ℕ} → Tower K n → Finset (Fin n → L) := by
  classical
  exact fun {n} T => match n,T with
    | _, .base => {fun i => Fin.elim0 i}
    | _, .adjoin prior f _ =>
        (solutions L prior).biUnion fun x =>
          (((f.map (MvPolynomial.aeval x).toRingHom).roots.toFinset).image (fun a => Fin.cons a x))

theorem mem_solutions_iff {n : ℕ} (T : Tower K n) (x : Fin n → L) :
    x ∈ solutions L T ↔ Satisfies T x := by
  classical
  induction T with
  | base =>
    simp only [solutions,Finset.mem_singleton,Satisfies,iff_true]
    exact Subsingleton.elim _ _
  | @adjoin n T f hf ih =>
    simp only [solutions,Finset.mem_biUnion,Finset.mem_image,Multiset.mem_toFinset,Satisfies]
    constructor
    · rintro ⟨y,hy,a,ha,rfl⟩
      simp only [Fin.tail_cons,Fin.cons_zero]
      exact ⟨(ih y).mp hy,(mem_roots (hf.map _).ne_zero).mp ha⟩
    · rintro ⟨hy,ha⟩
      exact ⟨Fin.tail x,(ih _).mpr hy,x 0,(mem_roots (hf.map _).ne_zero).mpr ha,Fin.cons_self_tail x⟩

/-- Product-of-degrees bound even when some equations have repeated roots. -/
theorem card_solutions_le (L : Type*) [Field L] [Algebra K L] {n : ℕ} (T : Tower K n) :
    (solutions L T).card ≤ T.degreeBound := by
  classical
  induction T with
  | base => simp [solutions,degreeBound]
  | @adjoin n T f hf ih =>
    simp only [solutions,degreeBound]
    apply (Finset.card_biUnion_le_card_mul _ _ f.natDegree ?_).trans (Nat.mul_le_mul_right _ ih)
    intro x hx
    exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans natDegree_map_le))

/-- Specializing polynomial coefficients commutes with every algebra homomorphism.
This also covers automorphisms of the geometric field and scalar extension from K. -/
theorem satisfies_map {M : Type*} [Field M] [Algebra K M] (φ : L →ₐ[K] M)
    {n : ℕ} (T : Tower K n) (x : Fin n → L) :
    Satisfies T (fun i => φ (x i)) ↔ Satisfies T x := by
  induction T with
  | base => rfl
  | @adjoin n T f hf ih =>
    have ce : φ.toRingHom.comp (MvPolynomial.aeval (R:=K) (Fin.tail x)).toRingHom =
        (MvPolynomial.aeval (R:=K) (fun i => φ (Fin.tail x i))).toRingHom := by
      exact congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval (R:=K) (Fin.tail x) φ)
    have hp : (f.map (MvPolynomial.aeval (R:=K) (Fin.tail x)).toRingHom).map φ.toRingHom =
        f.map (MvPolynomial.aeval (R:=K) (fun i => φ (Fin.tail x i))).toRingHom := by
      rw [Polynomial.map_map,ce]
    change (Satisfies T (fun i => φ (Fin.tail x i)) ∧
      (f.map (MvPolynomial.aeval (R:=K) (fun i => φ (Fin.tail x i))).toRingHom).eval (φ (x 0)) = 0) ↔ _
    rw [← hp]
    change (_ ∧ _ = _) ↔ (Satisfies T (Fin.tail x) ∧ _)
    rw [show φ (x 0) = φ.toRingHom (x 0) from rfl,eval_map_apply,map_eq_zero_iff _ φ.injective]
    exact and_congr (ih _) Iff.rfl

/-- Every such tower over ℚ has one monic rational polynomial describing existence of
a full rational tuple. Its degree is bounded by the product of the tower degrees.
The statement is after specialization of the data defining the tower. -/
theorem exists_projection {n : ℕ} (T : Tower ℚ n) :
    ∃ (b : ℕ) (p : ℚ[X]), b ≤ T.degreeBound.choose 2*(n-1) ∧ p.Monic ∧
      p.natDegree ≤ T.degreeBound ∧
      p.map (algebraMap ℚ (AlgebraicClosure ℚ)) = projection (solutions (AlgebraicClosure ℚ) T) b ∧
      ((∃ z : ℚ, p.IsRoot z) ↔ ∃ x : Fin n → ℚ, Satisfies T x) := by
  let L := AlgebraicClosure ℚ
  have stable : Stable ℚ (solutions L T) := by
    intro σ x hx
    rw [mem_solutions_iff] at hx ⊢
    exact (satisfies_map σ.toAlgHom T x).mpr hx
  obtain ⟨b,p,hb,hm,hd,hp,he⟩ := exists_rational_root_iff stable
  have hs := card_solutions_le L T
  refine ⟨b,p,hb.trans (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hs)),hm,hd.le.trans hs,hp,he.trans ?_⟩
  apply exists_congr
  intro x
  rw [mem_solutions_iff]
  exact satisfies_map (Algebra.ofId ℚ L) T x

end Tower
end
end ZInQBlueprint.SunTower
#print axioms ZInQBlueprint.SunTower.Tower.mem_solutions_iff
#print axioms ZInQBlueprint.SunTower.Tower.card_solutions_le
#print axioms ZInQBlueprint.SunTower.Tower.satisfies_map
#print axioms ZInQBlueprint.SunTower.Tower.exists_projection
