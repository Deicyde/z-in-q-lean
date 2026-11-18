import EndomorphismSpecialization
import PicardConjugation
import PicardSextic
import PicardLocal
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Specialization in the Picard family. The affine equation is the one
in Laga and Shnidman, Remark 2.12. In the isogeny category the two maps
splitting a projector lift from one fibre, including their identities. -/
namespace ZOverQ.Qualitative.Prym

open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def a (u v : K) : K := 2*(u^6-v^6)^2
def cubeRoot (u v : K) : K := -(u^6-v^6)*v^2

/-- The equation in Remark 2.12 after setting b=w³, retaining both sides. -/
def prymequation (a w x y : K) : Prop :=
  -a*w*y^2 = (x^2+2*x-2)*(w^3*x^4+4*w^3*x^3+2*(a^2-4*w^3)*x-(a^2-4*w^3))

omit [CharZero K] in
theorem parameters (u v : K) :
    cubeRoot u v ^ 3 = -(u^6-v^6)^3*v^6 ∧
    a u v ^ 2 - 4*cubeRoot u v ^ 3 = 4*(u^6-v^6)^3*u^6 := by
  unfold a cubeRoot; constructor <;> ring

omit [CharZero K] in
theorem endomorphism_parameter (i u v : K) (hi : i^2 = -1) :
    16*(cubeRoot u v)^3*((a u v)^2-4*(cubeRoot u v)^3) =
      (2*i*(u^6-v^6)*u*v)^6 := by
  rw [(parameters u v).2, (parameters u v).1]
  have h6 : i^6 = -1 := by rw [show 6=2*3 by decide,pow_mul,hi]; ring
  simp only [mul_pow,h6]; ring

theorem moduli_parameter {u v : K} (hv : v ≠ 0) (_ha : u^6-v^6 ≠ 0) :
    1 - (a u v)^2/(4*cubeRoot u v ^ 3) = u^6/v^6 := by
  unfold a
  rw [(parameters u v).1]
  field_simp [hv,_ha]
  ring

omit [CharZero K] in
/-- Dividing by the nonzero cube and changing y to vy gives exactly the
Picard sextic. The change of ordinate is invertible whenever v is nonzero. -/
theorem equation_iff {u v : K} (h : u^6-v^6 ≠ 0) (x y : K) :
    prymequation (a u v) (cubeRoot u v) x y ↔
      2*(v*y)^2 = (PicardLocal.sextic (u^6) (v^6)).eval x := by
  rw [prymequation, PicardLocal.sextic, eval_mul, PicardLocal.quartic_eval,PicardLocal.quadratic_eval]
  have e : -a u v*cubeRoot u v*y^2 -
      (x^2+2*x-2)*((cubeRoot u v)^3*x^4+4*(cubeRoot u v)^3*x^3+
        2*((a u v)^2-4*(cubeRoot u v)^3)*x-((a u v)^2-4*(cubeRoot u v)^3)) =
      (u^6-v^6)^3 * (2*(v*y)^2-(x^2+2*x-2)*(4*u^6*(2*x-1)-v^6*x^3*(x+4))) := by
    rw [(parameters u v).2,(parameters u v).1]
    unfold a cubeRoot; ring
  rw [← sub_eq_zero, e, mul_eq_zero]
  simp [h, sub_eq_zero]

/-- Over the coefficient field the invariant U/V can avoid every finite
exceptional set at rational parameters, even after deleting finitely many
rational parameters from the base. -/
theorem choose_reference {ρ : K} (hρ : ρ^2 = -3) (values : Finset K) (omitPoints : Finset ℚ) :
    ∃ s : ℚ, s ∉ omitPoints ∧ ((s:K)+ρ)^6/((s:K)-ρ)^6 ∉ values := by
  classical
  have non : ρ ≠ 0 := by intro h; rw [h] at hρ; norm_num at hρ
  let P (j : K) : K[X] := (X+C ρ)^6 - C j*(X-C ρ)^6
  have nonzero (j : K) : P j ≠ 0 := by
    intro h
    have e := congrArg (fun f : K[X] => f.eval ρ) h
    have nz : ρ+ρ ≠ 0 := by rw [← two_mul]; exact mul_ne_zero (by norm_num) non
    simp [P,nz] at e
  let forbidden := values.biUnion (fun j => (P j).roots.toFinset)
  have finite : Set.Finite ((fun s : ℚ => (s : K)) ⁻¹' (forbidden : Set K)) :=
    Set.Finite.preimage (Rat.cast_injective (α:=K)).injOn forbidden.finite_toSet
  obtain ⟨s,hs⟩ := (finite.union omitPoints.finite_toSet).exists_notMem
  refine ⟨s,fun h => hs (Or.inr h),fun h => hs (Or.inl ?_)⟩
  have nz : (s:K)-ρ ≠ 0 := by
    intro e
    have hsr := sub_eq_zero.mp e
    rw [← hsr] at hρ
    have hr : s^2 = (-3:ℚ) := by exact_mod_cast hρ
    nlinarith [sq_nonneg s]
  apply Finset.mem_biUnion.mpr
  refine ⟨_,h,Multiset.mem_toFinset.mpr ((mem_roots (nonzero _)).mpr ?_)⟩
  simp [P, IsRoot, nz]

end

section Quaternion

/-- For two presentations of a division quaternion algebra, the same nonzero
multiplier intertwines both pairs of generators. This gives the inner
correction to a conjugate isogeny when both presentations act on the fibre. -/
theorem intertwine_generators {D : Type*} [DivisionRing D] (i j I J : D)
    (hi : i ≠ 0) (hj : j ≠ 0) (iSquare : i*i = I*I) (jSquare : j*j = J*J)
    (central : ∀ w : D, Commute (j*j) w)
    (anti : j*i = -(i*j)) (anti' : J*I = -(I*J)) :
    ∃ w : D, w ≠ 0 ∧ w*i = I*w ∧ w*j = J*w := by
  have first : ∃ z : D, z ≠ 0 ∧ z*i=I*z := by
    by_cases hz : I+i=0
    · have eqn := eq_neg_of_add_eq_zero_left hz
      exact ⟨j,hj,by rw [eqn,neg_mul,anti]⟩
    · exact ⟨I+i,hz,by rw [add_mul,mul_add,iSquare,add_comm]⟩
  obtain ⟨z,hz,zi⟩ := first
  let t := J*z+z*j
  have tj : t*j=J*t := by
    simp only [t,add_mul,mul_add,mul_assoc]
    rw [← mul_assoc J J z,← jSquare,(central z).eq]
    exact add_comm _ _
  have ti : t*i= -(I*t) := by
    simp only [t,add_mul,mul_add,mul_assoc,zi,anti,mul_neg,neg_add_rev]
    rw [← mul_assoc J I z,anti',neg_mul,mul_assoc,← mul_assoc I z j,← zi,mul_assoc]
    abel
  by_cases zero : t = 0
  · have minus : J*z = -(z*j) := eq_neg_of_add_eq_zero_left zero
    refine ⟨z*i,mul_ne_zero hz hi,?_,?_⟩
    · rw [← mul_assoc I z i,← zi]
    · rw [← mul_assoc J z i,minus,neg_mul]
      simp only [mul_assoc,anti,mul_neg,neg_neg]
  · refine ⟨t*j,mul_ne_zero zero hj,?_,?_⟩
    · rw [mul_assoc,anti,mul_neg,← mul_assoc,ti,neg_mul,neg_neg,mul_assoc]
    · rw [← mul_assoc J t j,← tj]

/-- The correction intertwines the entire endomorphism algebra as soon as
these quaternion generators generate it over its centre. -/
theorem intertwine_algebra {A D : Type*} [DivisionRing A] [DivisionRing D]
    [Algebra ℚ A] [Algebra ℚ D] (f g : A →ₐ[ℚ] D) (i j : A) (a b : ℚ)
    (hi : i ≠ 0) (hj : j ≠ 0) (sqI : i*i = algebraMap ℚ A a) (sqJ : j*j = algebraMap ℚ A b)
    (anti : j*i = -(i*j)) (gen : Algebra.adjoin ℚ ({i,j} : Set A) = ⊤) :
    ∃ w : Dˣ, ∀ x : A, (w:D)*f x = g x*(w:D) := by
  have i2 (φ : A →ₐ[ℚ] D) : φ i * φ i = algebraMap ℚ D a := by rw [← map_mul,sqI,φ.commutes]
  have j2 (φ : A →ₐ[ℚ] D) : φ j * φ j = algebraMap ℚ D b := by rw [← map_mul,sqJ,φ.commutes]
  have ji (φ : A →ₐ[ℚ] D) : φ j * φ i = -(φ i * φ j) := by rw [← map_mul,anti,map_neg,map_mul]
  obtain ⟨w,h,wi,wj⟩ := intertwine_generators (f i) (f j) (g i) (g j)
    ((map_ne_zero f).mpr hi) ((map_ne_zero f).mpr hj) ((i2 f).trans (i2 g).symm) ((j2 f).trans (j2 g).symm)
    (fun x => j2 f ▸ Algebra.commutes b x) (ji f) (ji g)
  refine ⟨Units.mk0 w h,fun x => ?_⟩
  change w*f x = g x*w
  have hx : x ∈ Algebra.adjoin ℚ ({i,j} : Set A) := by rw [gen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    rcases Set.mem_insert_iff.mp hu with rfl|hj'
    · exact wi
    · obtain rfl := Set.mem_singleton_iff.mp hj'
      exact wj
  | algebraMap q => rw [f.commutes,g.commutes]; exact (Algebra.commutes q w).symm
  | add u v _ _ hu hv => rw [map_add,map_add,mul_add,add_mul,hu,hv]
  | mul u v _ _ hu hv => rw [map_mul,map_mul,← mul_assoc,hu,mul_assoc,hv,← mul_assoc]

end Quaternion

section Averaging
open LinearMap
variable {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]

/-- A quotient of rational projective representations with the same multiplier
has an equivariant section. Its projector is therefore invariant under the
conjugation action used in descent. -/
theorem split_projective_quotient (v : G → V ≃ₗ[ℚ] V) (w : G → W ≃ₗ[ℚ] W)
    (c : G → G → ℚˣ)
    (vcomp : ∀ g h x, v g (v h x) = (c g h : ℚ) • v (g*h) x)
    (wcomp : ∀ g h x, w g (w h x) = (c g h : ℚ) • w (g*h) x)
    (q : W →ₗ[ℚ] V) (surj : Function.Surjective q)
    (equiv : ∀ g x, q (w g x) = v g (q x)) :
    ∃ (j : V →ₗ[ℚ] W), (∀ x, q (j x) = x) ∧ (∀ g x, w g (j x) = j (v g x)) ∧
      (j.comp q).comp (j.comp q) = j.comp q ∧ ∀ g x, w g (j (q x)) = j (q (w g x)) := by
  classical
  obtain ⟨s,hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surj)
  let T (g : G) (l : V →ₗ[ℚ] W) := (w g).toLinearMap.comp (l.comp (v g).symm.toLinearMap)
  have act (g h : G) (l : V →ₗ[ℚ] W) : T g (T h l) = T (g*h) l := by
    ext x
    let y := (v h).symm ((v g).symm x)
    have pre : (c g h : ℚ) • y = (v (g*h)).symm x := by
      apply (v (g*h)).injective
      rw [map_smul,← vcomp,LinearEquiv.apply_symm_apply]
      simp
    change w g (w h (l y)) = w (g*h) (l ((v (g*h)).symm x))
    rw [wcomp,← pre,map_smul,map_smul]
  let j : V →ₗ[ℚ] W := ((Fintype.card G : ℚ)⁻¹) • ∑ h : G, T h s
  have section' (x : V) : q (j x)=x := by
    have term (h : G) : q (T h s x) = x := by
      change q (w h (s ((v h).symm x)))=x
      rw [equiv]
      exact (congrArg (v h) (LinearMap.congr_fun hs ((v h).symm x))).trans ((v h).apply_symm_apply x)
    simp only [j,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,term,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℚ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]
  have commute (g : G) (x : V) : w g (j x)=j (v g x) := by
    have term (h : G) : w g (T h s x) = T (g*h) s (v g x) := by
      have e := LinearMap.congr_fun (act g h s) (v g x)
      change w g (T h s ((v g).symm (v g x))) = _ at e
      simpa only [LinearEquiv.symm_apply_apply] using e
    simp only [j,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,term]
    rw [show (∑ h : G, T (g*h) s (v g x)) = ∑ h : G, T h s (v g x) from
      Equiv.sum_comp (Equiv.mulLeft g) (fun h => T h s (v g x))]
  refine ⟨j,section',commute,?_,fun g x => (commute g (q x)).trans (congrArg j (equiv g x).symm)⟩
  ext x
  simp only [comp_apply,section']

end Averaging

open CategoryTheory CategoryTheory.Limits ZOverQ.Qualitative.Specialization

section Lifting
variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
  [HasZeroMorphisms D] [HasFiniteBiproducts C]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms] {I J : Type} [Finite I] [Finite J]
variable (X : I → C) (Y : J → C) [PreservesBiproduct X F] [PreservesBiproduct Y F]
variable {Z : C} (x : ∀ i, X i ≅ Z) (y : ∀ j, Y j ≅ Z)
variable (atReference : Function.Bijective (fun a : Z ⟶ Z => F.map a))
include x y atReference

/-- Full faithfulness on a reference factor controls rectangular matrices
of morphisms between two finite products of its conjugates. -/
theorem biproduct_hom_bijective :
    Function.Bijective (fun a : ⨁ X ⟶ ⨁ Y => F.map a) := by
  have entry (i j) := hom_bijective_of_reference F (x i) (y j) atReference
  constructor
  · intro a b h
    apply (biproduct.matrixEquiv (f:=X) (g:=Y)).injective
    funext i j
    apply (entry i j).1
    change F.map (biproduct.ι X i ≫ a ≫ biproduct.π Y j) =
      F.map (biproduct.ι X i ≫ b ≫ biproduct.π Y j)
    simp only [F.map_comp,h]
  · intro b
    let entries i j := F.map (biproduct.ι X i) ≫ b ≫ F.map (biproduct.π Y j)
    choose a ha using fun i j => (entry i j).2 (entries i j)
    refine ⟨biproduct.matrix a,?_⟩
    apply (isBilimitOfPreserves F (biproduct.isBilimit X)).isColimit.hom_ext
    intro i
    apply (isBilimitOfPreserves F (biproduct.isBilimit Y)).isLimit.hom_ext
    intro j
    change (F.map (biproduct.ι X i.as) ≫ F.map (biproduct.matrix a)) ≫ F.map (biproduct.π Y j.as)
      = (F.map (biproduct.ι X i.as) ≫ b) ≫ F.map (biproduct.π Y j.as)
    rw [Category.assoc,Category.assoc,← F.map_comp,← F.map_comp]
    change F.map (biproduct.components (biproduct.matrix a) i.as j.as) = entries i.as j.as
    rw [biproduct.matrix_components]
    exact ha i.as j.as

/-- Lift the two splitting maps seen at a single fibre. If p has already
descended, its geometric image is the specified power of the Jacobian. -/
theorem lift_splitting (p : ⨁ X ⟶ ⨁ X)
    (i₀ : F.obj (⨁ Y) ⟶ F.obj (⨁ X)) (r₀ : F.obj (⨁ X) ⟶ F.obj (⨁ Y))
    (left : i₀ ≫ r₀ = 𝟙 _) (right : r₀ ≫ i₀ = F.map p) :
    ∃ (i : ⨁ Y ⟶ ⨁ X) (r : ⨁ X ⟶ ⨁ Y),
      F.map i = i₀ ∧ F.map r = r₀ ∧ i ≫ r = 𝟙 _ ∧ r ≫ i = p := by
  obtain ⟨i,hi⟩ := (biproduct_hom_bijective F Y X y x atReference).2 i₀
  obtain ⟨r,hr⟩ := (biproduct_hom_bijective F X Y x y atReference).2 r₀
  change F.map i = i₀ at hi
  change F.map r = r₀ at hr
  refine ⟨i,r,hi,hr,(biproduct_end_bijective_of_reference F Y y atReference).1 ?_,
    (biproduct_end_bijective_of_reference F X x atReference).1 ?_⟩
  · change F.map (i ≫ r) = F.map (𝟙 _)
    rw [F.map_comp,hi,hr,left,F.map_id]
  · change F.map (r ≫ i) = F.map p
    rw [F.map_comp,hi,hr,right]

/-- Any image of the lifted projector is isomorphic to this power. -/
theorem factor_iso_power (p : ⨁ X ⟶ ⨁ X) {B : C} (iB : B ⟶ ⨁ X) (rB : ⨁ X ⟶ B)
    (hB : iB ≫ rB = 𝟙 B) (hp : rB ≫ iB = p)
    (i₀ : F.obj (⨁ Y) ⟶ F.obj (⨁ X)) (r₀ : F.obj (⨁ X) ⟶ F.obj (⨁ Y))
    (left : i₀ ≫ r₀ = 𝟙 _) (right : r₀ ≫ i₀ = F.map p) : Nonempty (B ≅ ⨁ Y) := by
  obtain ⟨i,r,_,_,hi,hr⟩ := lift_splitting F X Y x y atReference p i₀ r₀ left right
  exact ⟨⟨iB ≫ r,i ≫ rB,by calc
    (iB ≫ r) ≫ i ≫ rB = iB ≫ (r ≫ i) ≫ rB := by simp only [Category.assoc]
    _ = 𝟙 B := by rw [hr,← hp]; simp only [← Category.assoc,hB,Category.id_comp],
    by calc
    (i ≫ rB) ≫ iB ≫ r = i ≫ (rB ≫ iB) ≫ r := by simp only [Category.assoc]
    _ = 𝟙 _ := by rw [hp,← hr]; simp only [← Category.assoc,hi,Category.id_comp]⟩⟩

end Lifting
end ZOverQ.Qualitative.Prym

#print axioms ZOverQ.Qualitative.Prym.parameters
#print axioms ZOverQ.Qualitative.Prym.endomorphism_parameter
#print axioms ZOverQ.Qualitative.Prym.moduli_parameter
#print axioms ZOverQ.Qualitative.Prym.equation_iff
#print axioms ZOverQ.Qualitative.Prym.choose_reference
#print axioms ZOverQ.Qualitative.Prym.intertwine_generators
#print axioms ZOverQ.Qualitative.Prym.intertwine_algebra
#print axioms ZOverQ.Qualitative.Prym.lift_splitting
#print axioms ZOverQ.Qualitative.Prym.factor_iso_power

#print axioms ZOverQ.Qualitative.Prym.split_projective_quotient
