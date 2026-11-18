import PicardCM
import QuaternionModel

/-!
# The full quaternion algebra over one number field

In the equation of Laga and Shnidman, Remark 2.12, replace `a,w` by
`λ³a,λ²w`, with `λ=v²/d`. The normalized genus-two polynomial then agrees
coefficient by coefficient with the rationally twisted Picard sextic. Its
marked invariant is unchanged and its endomorphism parameter remains a sixth
power over the same field for every rational twist.

The universal arithmetic-geometric input is the characteristic-zero
consequence of Remark 2.12, Lemma 6.2 and Corollary 6.6 of
https://doi.org/10.1112/jlms.70347, with simplicity transported by an
isogeny and with the rational endomorphism algebras of isogenous varieties
identified by conjugation.
-/
namespace ZOverQ.Qualitative.PicardPrym
open CategoryTheory AlgebraicGeometry Polynomial IntermediateField
open ZInQBlueprint.AbelianModel ZInQ ZInQ.QualitativeHeight
open PicardConjugation PicardDescent PicardLocalization PicardLocal PicardConjugateEnd PicardCM
open scoped ZInQBlueprint.NormalDescent TensorProduct
noncomputable section

/-- The normalized right-hand side of the genus-two equation in Remark 2.12,
in the order of powers of x used in that remark. The parameter b is w³. -/
def publishedPolynomial {K : Type*} [Field K] (a w : K) : K[X] :=
  C ((-a*w)⁻¹) * quadratic * (C (w^3)*X^4+4*C (w^3)*X^3+2*C (a^2-4*w^3)*X-C (a^2-4*w^3))

section Arithmetic
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem disc_scale (a w l : K) :
    (l^3*a)^2-4*(l^2*w)^3=l^6*(a^2-4*w^3) := by ring

omit [CharZero K] in
private theorem sextic_factor (u v l : K) :
    -(l^3*Prym.a u v)*(l^2*Prym.cubeRoot u v)=2*l^5*(u^6-v^6)^3*v^2 := by
  unfold Prym.a Prym.cubeRoot; ring

private theorem scaled_model {u v l : K} (hv : v ≠ 0) (hΔ : u^6-v^6 ≠ 0) (hl : l ≠ 0) :
    publishedPolynomial (l^3*Prym.a u v) (l^2*Prym.cubeRoot u v) =
      C (l/(2*v^2)) * sextic (u^6) (v^6) := by
  apply Polynomial.funext
  intro x
  simp only [publishedPolynomial,eval_mul,eval_C,eval_add,eval_sub,eval_pow,eval_X,eval_ofNat,
    sextic,quartic_eval]
  rw [sextic_factor,disc_scale,(Prym.parameters u v).2]
  rw [show (l^2*Prym.cubeRoot u v)^3=l^6*(-(u^6-v^6)^3*v^6) by
    rw [mul_pow,(Prym.parameters u v).1]; ring]
  field_simp [hΔ,hl,hv]
  ring

/-- Literal equality of the two normalized polynomials. The maps of
coordinate rings preserve both x and y. -/
theorem twisted_polynomial {u v d : K} (hv : v ≠ 0) (hΔ : u^6-v^6 ≠ 0) (hd : d ≠ 0) :
    let l := v^2/d
    publishedPolynomial (l^3*Prym.a u v) (l^2*Prym.cubeRoot u v) =
      sextic (u^6/(2*d)) (v^6/(2*d)) := by
  dsimp only
  rw [scaled_model hv hΔ (div_ne_zero (pow_ne_zero 2 hv) hd),← LocalSupport.sextic_scale]
  apply congrArg₂ sextic <;> field_simp

/-- Smooth marked Picard data, including the exact sixth root required by
Corollary 6.6, for every nonzero twist in the ground field. -/
theorem twisted_parameters {u v d i : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (hΔ : u^6-v^6 ≠ 0) (hd : d ≠ 0) (hi : i^2 = -1) :
    let l := v^2/d
    let a := l^3*Prym.a u v
    let w := l^2*Prym.cubeRoot u v
    a ≠ 0 ∧ w ≠ 0 ∧ a^2-4*w^3 ≠ 0 ∧
      1-a^2/(4*w^3)=u^6/v^6 ∧ (l^2*(2*i*(u^6-v^6)*u*v))^6=16*w^3*(a^2-4*w^3) := by
  let l := v^2/d
  have h : l ≠ 0 := div_ne_zero (pow_ne_zero 2 hv) hd
  have hn : Prym.cubeRoot u v ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hΔ) (pow_ne_zero _ hv)
  have ha : Prym.a u v ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hΔ)
  dsimp only
  refine ⟨mul_ne_zero (pow_ne_zero _ h) ha,mul_ne_zero (pow_ne_zero _ h) hn,?_,?_,?_⟩
  · rw [disc_scale,(Prym.parameters u v).2]
    exact mul_ne_zero (pow_ne_zero _ h) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hΔ)) (pow_ne_zero _ hu))
  · rw [← Prym.moduli_parameter hv hΔ]
    change 1-(l^3*Prym.a u v)^2/(4*(l^2*Prym.cubeRoot u v)^3) = _
    field_simp [h,hn]
  · rw [disc_scale]
    calc
      _ = l^12*(2*i*(u^6-v^6)*u*v)^6 := by ring
      _ = l^12*(16*(Prym.cubeRoot u v)^3*((Prym.a u v)^2-4*(Prym.cubeRoot u v)^3)) := by
        rw [Prym.endomorphism_parameter i u v hi]
      _ = _ := by ring
end Arithmetic

/-- Laga–Shnidman's genus-two consequence over a sextic splitting field.
The quadratic equation asserts that the field contains a primitive cube
root of unity. In characteristic zero the geometric simplicity of this
abelian surface is equivalent to the absence of an elliptic subgroup. -/
def PublishedPrymEndomorphisms : Prop :=
  ∀ (L : FiniteGaloisIntermediateField ℚ Qbar) (a w : L), a ≠ 0 → w ≠ 0 → a^2-4*w^3 ≠ 0 →
    (∃ o : L, o^2+o+1=0) → (∃ ε : L, ε^6=16*w^3*(a^2-4*w^3)) →
    ∀ (deg : (publishedPolynomial a w).natDegree = 6) (sep : (publishedPolynomial a w).Separable)
      (Y : GroupScheme L), Nonempty (Y ≅ completionJacobian _ deg sep) →
      ¬HasEllipticSubgroup ((baseChange L.toIntermediateField.val.toRingHom).obj Y) →
      Nonempty (QuaternionModel Y)

private theorem subgroup_transport {A B : GroupScheme Qbar} (e : A ≅ B)
    (h : HasEllipticSubgroup A) : HasEllipticSubgroup B := by
  obtain ⟨E,abel,dim,f,closed⟩ := h
  let : IsClosedImmersion f.hom.hom.hom.left := closed
  let : IsIso e.hom.hom.hom.hom.left := ⟨⟨e.inv.hom.hom.hom.left,
    congrArg (fun g : A ⟶ A => g.hom.hom.hom.left) e.hom_inv_id,
    congrArg (fun g : B ⟶ B => g.hom.hom.hom.left) e.inv_hom_id⟩⟩
  exact ⟨E,abel,dim,f ≫ e.hom,show IsClosedImmersion (f.hom.hom.hom.left ≫ e.hom.hom.hom.hom.left)
    from inferInstance⟩

/-- The ordinary fibre and the quadratic twist use the same field of
definition for every geometric rational endomorphism. -/
theorem family_quaternion (published : PublishedPrymEndomorphisms) (L : FiniteGaloisIntermediateField ℚ Qbar)
    (hKL : fixedField ≤ L.toIntermediateField) (i : L) (hi : i^2 = -1) (t d : ℚ)
    (ht : t ∉ contactSet) (hd : d ≠ 0) (hn : ¬HasEllipticSubgroup (geometricFibre t d ht hd)) :
    Nonempty (QuaternionModel (familyOver (IntermediateField.inclusion hKL) t d ht hd)) := by
  let ψ := IntermediateField.inclusion hKL
  let φ := L.toIntermediateField.val.toRingHom
  let s := picardParameter t
  let u := ψ ((s:fixedField)+ρ)
  let v := ψ ((s:fixedField)-ρ)
  let l := v^2/(d:L)
  let a := l^3*Prym.a u v
  let w := l^2*Prym.cubeRoot u v
  let U₀ := U s/(2*(d:fixedField))
  let V₀ := V s/(2*(d:fixedField))
  obtain ⟨hU,hV,hδ⟩ := regular t ht
  have u6 : u^6=ψ (U s) := (map_pow ψ _ 6).symm
  have v6 : v^6=ψ (V s) := (map_pow ψ _ 6).symm
  have hu : u ≠ 0 := fun eq => ((map_ne_zero_iff ψ ψ.injective).mpr hU) (by
    rw [← u6,eq]; norm_num)
  have hv : v ≠ 0 := fun eq => ((map_ne_zero_iff ψ ψ.injective).mpr hV) (by
    rw [← v6,eq]; norm_num)
  have hΔ : u^6-v^6 ≠ 0 := by rw [u6,v6,← map_sub]; exact (map_ne_zero_iff _ ψ.injective).mpr hδ
  have hdL : (d:L) ≠ 0 := Rat.cast_ne_zero.mpr hd
  obtain ⟨ha,hw,hdc,_,root⟩ := twisted_parameters hu hv hΔ hdL hi
  have unity : ∃ o : L, o^2+o+1=0 := by
    refine ⟨(ψ ρ-1)/2,?_⟩
    have e : (ψ ρ)^2 = -3 := by rw [← map_pow,rho_sq,map_neg,map_ofNat]
    linear_combination (1/4) * e
  have scale : publishedPolynomial a w = C ((1:L)^2) * (sextic U₀ V₀).map ψ.toRingHom := by
    rw [twisted_polynomial hv hΔ hdL,one_pow,map_one,one_mul,PicardLocal.sextic_map]
    simp only [U₀,V₀,u6,v6,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_div₀,map_mul,map_ofNat,map_ratCast]
  have c₀ : 2*(d:fixedField) ≠ 0 := mul_ne_zero (by norm_num) (Rat.cast_ne_zero.mpr hd)
  have ha₀ : U₀ ≠ 0 := div_ne_zero hU c₀
  have hb₀ : V₀ ≠ 0 := div_ne_zero hV c₀
  have hδ₀ : U₀-V₀ ≠ 0 := by
    dsimp only [U₀,V₀]; rw [← sub_div]
    exact div_ne_zero hδ c₀
  obtain ⟨deg,sep,iso⟩ := jacobian_scalar_square ψ.toRingHom U₀ V₀ ha₀ hb₀ hδ₀ _ 1 one_ne_zero scale
  apply published L a w ha hw hdc unity ⟨_,root⟩ deg sep _ iso
  intro h
  let J := familyJacobian t d ht hd (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
  let e := (WittAscent.baseChangeCompIso ψ.toRingHom φ J).symm
  exact hn (subgroup_transport e h)

private def imaginaryRoot : Qbar :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (-1:Qbar) (by decide : 0<2))

private theorem imaginaryRoot_sq : imaginaryRoot^2 = -1 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-1:Qbar) (by decide : 0<2))

open IntermediateField in
private theorem imaginary_galois : IsGalois ℚ ℚ⟮imaginaryRoot⟯ where
  to_normal := by
    apply IntermediateField.normal_iff_forall_map_le.mpr
    intro σ
    rw [IntermediateField.adjoin_map,Set.image_singleton,IntermediateField.adjoin_simple_le_iff]
    have e : (σ imaginaryRoot)^2=imaginaryRoot^2 := by
      rw [← map_pow,imaginaryRoot_sq,map_neg,map_one]
    have h := IntermediateField.mem_adjoin_simple_self ℚ imaginaryRoot
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with e | e
    · simpa only [e] using h
    · rw [e]; exact neg_mem h

open IntermediateField in
/-- The single finite Galois field ℚ(√−2,√−3,i) for all rational fibres and
all rational twists. -/
def standardField : FiniteGaloisIntermediateField ℚ Qbar := by
  letI : IsGalois ℚ ℚ⟮imaginaryRoot⟯ := imaginary_galois
  letI : FiniteDimensional ℚ ℚ⟮imaginaryRoot⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R:=ℚ) imaginaryRoot)
  exact ⟨fixedField ⊔ ℚ⟮imaginaryRoot⟯⟩

theorem fixed_le : fixedField ≤ standardField.toIntermediateField := le_sup_left

def I : standardField := ⟨imaginaryRoot,
  (show ℚ⟮imaginaryRoot⟯ ≤ standardField.toIntermediateField from le_sup_right)
    (IntermediateField.mem_adjoin_simple_self ℚ imaginaryRoot)⟩

theorem I_sq : I^2 = -1 := Subtype.ext imaginaryRoot_sq

/-- One finite exceptional set and one explicitly generated field for the
entire family. -/
theorem quaternion_outside_finite (published : PublishedPrymEndomorphisms)
    (finite : {j : Qbar | j ∈ splitValues ∧ Module.finrank ℚ ℚ⟮j⟯ ≤ 2}.Finite) :
    ∃ T : Finset ℚ, T.card ≤ 6*finite.toFinset.card ∧
      ∀ (t d : ℚ) (ht : t ∉ contactSet) (hd : d ≠ 0), t ∉ T →
      Nonempty (QuaternionModel (familyOver (IntermediateField.inclusion fixed_le) t d ht hd)) := by
  obtain ⟨T,cap,crit⟩ := nonsimple_fibres finite
  exact ⟨T,cap,fun t d ht hd hT => family_quaternion published standardField fixed_le I I_sq t d ht hd
    (fun h => hT ((crit t d ht hd).mpr h))⟩

end
end ZOverQ.Qualitative.PicardPrym
#print axioms ZOverQ.Qualitative.PicardPrym.twisted_polynomial
#print axioms ZOverQ.Qualitative.PicardPrym.twisted_parameters
#print axioms ZOverQ.Qualitative.PicardPrym.family_quaternion

#print axioms ZOverQ.Qualitative.PicardPrym.quaternion_outside_finite
