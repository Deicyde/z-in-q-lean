import CoarseConic

/-! Eliminate the common choice of scale for the Igusa modular forms on the
discriminant-six family. Normalized algebraic coordinates and the comparison
scale may be taken in different fields. -/
namespace ZInQBlueprint.IgusaRatio
open scoped BigOperators
open ZInQBlueprint
variable {K E : Type*} [Field K] [Field E] [CharZero E]

omit [CharZero E] in
/-- The half-weight scale b multiplies J₂, J₄ and J₁₀ by b, b² and b⁵. -/
theorem psi_four (b j : E) :
    (b*(12*(j+1)))^2 - 24*b^2*(6*(j^2+j+1)) = 144*b^2*j := by ring

/-- Pull back the weight-four and weight-ten theta identities along one
embedding. The ten algebraic representatives may share an arbitrary scale. -/
structure ThetaIdentities (φ : K →+* E) (j : K) (z : Fin 10 → K) where
  scale : Eˣ
  weightFour : (∑ i, φ (z i)^8) / 4 =
    ((scale:E)*(12*(φ j+1)))^2 - 24*(scale:E)^2*(6*((φ j)^2+φ j+1))
  weightTen : -(∏ i, φ (z i))^2 / 16384 = -(scale:E)^5 * (φ j)^3 / 4

theorem quotient {φ : K →+* E} {j : K} {z : Fin 10 → K}
    (hj : j ≠ 0) (w : ThetaIdentities φ j z) :
    (∑ i, z i^8)^5 ≠ 0 ∧ j = 3779136 * (∏ i, z i)^4 / (∑ i, z i^8)^5 := by
  have h4 := w.weightFour
  rw [psi_four] at h4
  have hS : (∑ i, φ (z i)^8) = 576*(w.scale:E)^2*(φ j) := by
    linear_combination 4*h4
  have hP : (∏ i, φ (z i))^2 = 4096*(w.scale:E)^5*(φ j)^3 := by
    linear_combination -16384*w.weightTen
  have hSne : (∑ i, φ (z i)^8) ≠ 0 := by
    rw [hS]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ w.scale.ne_zero))
      ((map_ne_zero φ).2 hj)
  have hmap : φ (∑ i, z i^8) = ∑ i, φ (z i)^8 := by simp
  have hd : (∑ i, z i^8)^5 ≠ 0 := pow_ne_zero _ fun h => hSne (by rw [← hmap,h,map_zero])
  refine ⟨hd, (eq_div_iff hd).2 (φ.injective ?_)⟩
  simp only [map_mul,map_pow,map_sum,map_prod,map_ofNat]
  rw [hS, show (∏ i, φ (z i))^4 = ((∏ i, φ (z i))^2)^2 by ring, hP]
  ring

theorem unmarked_quotient [CharZero K] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    {φ : K →+* E} {z : Fin 10 → K} (w : ThetaIdentities φ (SixContact.J u : K) z) :
    (∑ i, z i^8)^5 ≠ 0 ∧
      (SixContact.J u : K) = 3779136 * (∏ i, z i)^4 / (∑ i, z i^8)^5 :=
  quotient (by exact_mod_cast (CoarseConic.unmarked_range hu).2.ne) w

/-- Streng's third absolute invariant in any common weighted representative
of the Baba–Granath vector. The common half-weight scale disappears. -/
theorem absolute_of_normalized (j b : E) (hj : j ≠ 0) (hb : b ≠ 0) :
    (4*((b*(12*(j+1)))^2 - 24*b^2*(6*(j^2+j+1))))^5 /
      (4096*(b^5*j^3))^2 = 3779136/j := by
  rw [psi_four]
  field_simp [hj,hb]
  ring

/-- A single absolute invariant determines the quotient. Only its
denominator, the product of even theta nulls, needs to be known nonzero. -/
theorem quotient_of_absolute {φ : K →+* E} {j : K} {z : Fin 10 → K}
    (hj : j ≠ 0) (hprod : (∏ i, φ (z i)) ≠ 0)
    (hi : (∑ i, φ (z i)^8)^5 / (∏ i, φ (z i))^4 = 3779136 / φ j) :
    (∑ i, z i^8)^5 ≠ 0 ∧ j = 3779136 * (∏ i, z i)^4 / (∑ i, z i^8)^5 := by
  have hj' := (map_ne_zero φ).2 hj
  have he := (div_eq_div_iff (pow_ne_zero _ hprod) hj').mp hi
  have hs : (∑ i, φ (z i)^8)^5 ≠ 0 := fun h =>
    (mul_ne_zero (by norm_num : (3779136:E) ≠ 0) (pow_ne_zero _ hprod)) (by
      rw [h,zero_mul] at he; exact he.symm)
  have hd : (∑ i, z i^8)^5 ≠ 0 := fun h =>
    hs (by simpa only [map_pow,map_sum,map_zero] using congrArg φ h)
  refine ⟨hd, (eq_div_iff hd).2 (φ.injective ?_)⟩
  simpa only [map_mul,map_pow,map_sum,map_prod,map_ofNat,mul_comm (φ j)] using he

end ZInQBlueprint.IgusaRatio

#print axioms ZInQBlueprint.IgusaRatio.psi_four
#print axioms ZInQBlueprint.IgusaRatio.quotient
#print axioms ZInQBlueprint.IgusaRatio.unmarked_quotient
#print axioms ZInQBlueprint.IgusaRatio.absolute_of_normalized
#print axioms ZInQBlueprint.IgusaRatio.quotient_of_absolute
