import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! The common dyadic quadratic field and congruence used in TYZ Lemma 3.18. -/
namespace ZInQBlueprint.TYZ.Dyadic
noncomputable section
open Polynomial IntermediateField

/-- A normalized local scale for every positive integer in residue class five.
It carries √−5 to √−n and is 1 modulo 4. -/
theorem normalized_scale (n : ℕ) (hn : n%8=5) :
    ∃ c t : ℤ_[2], c = 1+4*t ∧ (5:ℤ_[2])*c^2 = n := by
  let f : Polynomial ℤ := C 5 * X^2 - C (n:ℤ)
  have eval_f : ∀ y : ℤ_[2], f.aeval y = 5*y^2 - n := by
    intro y
    simp [f,map_ofNat]
  have deriv : f.derivative.aeval (1:ℤ_[2]) = 10 := by
    norm_num [f,Polynomial.derivative_mul,Polynomial.derivative_pow,map_ofNat]
  have ten : ‖(10:ℤ_[2])‖ = (1:ℝ)/2 := by
    have h5 : ‖(5:ℤ_[2])‖ = 1 := (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 5)).mpr (by decide)
    rw [show (10:ℤ_[2])=2*5 by norm_num, norm_mul,h5,mul_one]
    exact (PadicInt.norm_p (p := 2)).trans (by norm_num)
  have dvd : (2^3 : ℤ) ∣ 5 - (n:ℤ) := by omega
  have small := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (n := 3) (k := 5-(n:ℤ))).mpr dvd
  have cond : ‖f.aeval (1:ℤ_[2])‖ < ‖f.derivative.aeval (1:ℤ_[2])‖^2 := by
    rw [eval_f,deriv,ten]
    norm_num at small ⊢
    linarith
  obtain ⟨c,hc,hnear,_,_⟩ := hensels_lemma cond
  have hval : (5:ℤ_[2])*c^2 = n := sub_eq_zero.mp ((eval_f c).symm.trans hc)
  rw [deriv,ten] at hnear
  have hle : ‖c-1‖ ≤ (2:ℝ)^(-(2:ℤ)) := by
    apply (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ _).mpr
    norm_num; exact hnear
  have mem : c-1 ∈ Ideal.span {(2:ℤ_[2])^2} := by
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp hle
  obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp mem
  refine ⟨c,t,?_,hval⟩
  linear_combination ht

/-- All completions Q₂(√−n) with n≡5 mod 8 are the same embedded subfield
of an ambient extension once the square roots have been chosen. -/
theorem local_quadratic_field {M : Type*} [Field M] [Algebra ℚ_[2] M]
    (n : ℕ) (hn : n%8=5) {a b : M} (ha : a^2 = -(n:M)) (hb : b^2 = -5) :
    IntermediateField.adjoin ℚ_[2] {a} = IntermediateField.adjoin ℚ_[2] {b} := by
  obtain ⟨c,t,hc,he⟩ := normalized_scale n hn
  let j := algebraMap ℚ_[2] M
  let u := j (c:ℚ_[2])
  have heq : (5:ℚ_[2])*(c:ℚ_[2])^2 = n := by
    simpa only [map_mul,map_pow,map_ofNat,map_natCast,PadicInt.Coe.ringHom_apply] using
      congrArg (PadicInt.Coe.ringHom (p := 2)) he
  have scale : (5:M)*u^2 = n := by simpa [u,j,map_ofNat] using congrArg j heq
  have hroot : a^2 = (u*b)^2 := by rw [ha,mul_pow,hb]; linear_combination scale
  have u0 : u ≠ 0 := by
    intro h
    have hpos : (n:M) ≠ 0 := by
      have hnq : (n:ℚ_[2]) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      simpa using ((_root_.map_ne_zero j).mpr hnq)
    rw [h] at scale
    exact hpos (by simpa using scale.symm)
  have uf (F : IntermediateField ℚ_[2] M) : u ∈ F := F.algebraMap_mem _
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_)
    have m := (IntermediateField.adjoin ℚ_[2] {b}).mul_mem
      (uf _) (IntermediateField.mem_adjoin_simple_self _ b)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hroot with hr | hr
    · rwa [hr]
    · rw [hr]; exact (IntermediateField.adjoin ℚ_[2] {b}).neg_mem m
  · apply IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_)
    let F := IntermediateField.adjoin ℚ_[2] {a}
    have ma : a ∈ F := IntermediateField.mem_adjoin_simple_self _ a
    have m : u*b ∈ F := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hroot with hr | hr
      · rwa [←hr]
      · rw [hr] at ma
        simpa using F.neg_mem ma
    have := F.div_mem m (uf F)
    simpa [u0] using this

/-- Inside every dyadic algebra the compatible roots yield the same
ring-class generator modulo 8, hence also modulo 4. The symbols are ordinary
elements of the algebra before applying local reciprocity. -/
theorem common_generator_mod_eight {R : Type*} [CommRing R] [Algebra ℤ_[2] R]
    (n : ℕ) (hn : n%8=5) {b : R} (hb : b^2 = -5) :
    ∃ a : R, a^2 = -(n:R) ∧ (8:R) ∣ (1+2*(a-1)) - (1+2*(b-1)) := by
  obtain ⟨c,t,hc,he⟩ := normalized_scale n hn
  let j := algebraMap ℤ_[2] R
  have eq : (5:R) * (j c)^2 = n := by simpa [j,map_ofNat] using congrArg j he
  have jh : j c = 1+4*j t := by simpa [j,map_ofNat] using congrArg j hc
  refine ⟨j c*b,?_,j t*b,?_⟩
  · rw [mul_pow,hb]; linear_combination -eq
  · rw [jh]; ring

/-- The norm of the unit 1+2(√−n−1) is 1+4n, a residue class five modulo
eight. In particular its norm character distinguishes √2 from i. -/
theorem generator_norm (n : ℕ) (hn : n%8=5) {R : Type*} [CommRing R]
    {a : R} (ha : a^2 = -(n:R)) :
    (1+2*(a-1))*(1+2*(-a-1)) = 1+4*(n:R) ∧ (1+4*n)%8=5 := by
  refine ⟨?_,by omega⟩
  linear_combination -4*ha

/-- On the eighth roots, exponent 1+4n gives the same cyclotomic
exponent as its geometric inverse. It fixes the fourth root and reverses the
sign of the element z−z³ whose square is two. -/
theorem generator_cyclotomic_values {R : Type*} [CommRing R] (n : ℕ) (hn : n%8=5)
    {z : R} (hz : z^4 = -1) :
    let a := 1+4*n
    (a*a)%8 = 1 ∧ z^a = -z ∧ (z^a)^2=z^2 ∧ (z^a)-(z^a)^3=-(z-z^3) ∧ (z-z^3)^2=2 := by
  dsimp only
  have hmod : (1+4*n)%8=5 := by omega
  have he : 1+4*n = 5+8*((1+4*n)/8) := by omega
  have h8 : z^8=1 := by
    rw [show 8 = 4*2 by decide,pow_mul,hz]; ring
  have hneg : z^(1+4*n) = -z := by
    rw [he,pow_add,pow_mul,h8,one_pow,mul_one,show 5=4+1 by decide,pow_succ,hz,neg_one_mul]
  refine ⟨?_,hneg,?_,?_,?_⟩
  · rw [Nat.mul_mod,hmod]
  · rw [hneg]; ring
  · rw [hneg]; ring
  · linear_combination (z^2-2)*hz

end
end ZInQBlueprint.TYZ.Dyadic
#print axioms ZInQBlueprint.TYZ.Dyadic.normalized_scale
#print axioms ZInQBlueprint.TYZ.Dyadic.local_quadratic_field
#print axioms ZInQBlueprint.TYZ.Dyadic.common_generator_mod_eight
#print axioms ZInQBlueprint.TYZ.Dyadic.generator_norm
#print axioms ZInQBlueprint.TYZ.Dyadic.generator_cyclotomic_values
