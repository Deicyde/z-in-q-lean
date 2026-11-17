import TwistConverse
import ZInQKernel.Multiplication.Soundness.RationalHeights

/-! Equivalence, with explicit changes of constants, between the public
exponent-24 height estimate and a uniform rational-point bound on the twists. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section

private theorem constants_height :
    ratHeight 0=0 ∧ ratHeight 5=Real.log 5 ∧ ratHeight 120=Real.log 120 ∧
    Real.log 5+Real.log 120+Real.log 3=Real.log 1800 := by
  constructor
  · norm_num [ratHeight]
  constructor
  · norm_num [ratHeight]
  constructor
  · norm_num [ratHeight]
  · rw [←Real.log_mul (by norm_num) (by norm_num),←Real.log_mul (by norm_num) (by norm_num)]
    norm_num

theorem changes_height (x : ℚ) : ratHeight (X x) ≤ ratHeight x + Real.log 1800 ∧
    ratHeight (120/(x-5)) ≤ ratHeight x + Real.log 1800 := by
  obtain ⟨h0,h5,h120,log⟩ := constants_height
  have ha := ratHeight_add3_le 5 (120/x) 0
  have hb := ratHeight_div_le 120 x
  have hc := ratHeight_add3_le x (-5) 0
  have hd := ratHeight_div_le 120 (x-5)
  simp only [add_zero,h0,h5,h120,ratHeight_neg,←sub_eq_add_neg] at ha hb hc hd
  unfold X
  constructor <;> linarith

/-- When the fixed set absorbs 2,3,5 the public odd support divides the
absolute twisting integer. The reverse divisibility holds up to fixed primes. -/
theorem contact_dvd_kernel {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e)
    (S : Finset ℕ) (small : ∀ p : ℕ, p.Prime → p ∉ S → 5<p) :
    contactSupport S u ∣ d.natAbs := by
  classical
  unfold contactSupport
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ d.natAbs.primeFactors id ?_) (Nat.prod_primeFactors_dvd _)
  intro p hp
  obtain ⟨factor,hS,t,ht,pos,odd⟩ := Finset.mem_filter.mp hp
  have prime := Nat.prime_of_mem_primeFactors factor
  apply Nat.mem_primeFactors.mpr
  refine ⟨prime,?_,by simpa using (Kernel_nonzero hu h).1⟩
  apply (kernel_prime_iff hu h S prime hS (small p prime hS)).mpr
  exact (prime_dvd_contactSupport_iff hu prime).mpr ⟨hS,t,ht,pos,odd⟩

def TwistBound (H : ℝ) : Prop :=
  ∀ (d : ℤ) (x y : ℚ), Squarefree d → y≠0 → x≠5 → 30*(d:ℚ)*y^2=quintic x →
    ratHeight x ≤ H*(d.natAbs:ℝ)^24

def ContactBound (S : Finset ℕ) (A : ℝ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ A*(contactSupport S u:ℝ)^24

theorem contact_of_twists (S : Finset ℕ) (ps : ∀ p ∈ S, p.Prime)
    {H : ℝ} (hH : 0 ≤ H) (bound : TwistBound H) :
    ContactBound S (H*((∏ p ∈ S,p:ℕ):ℝ)^24 + Real.log 1800) := by
  intro u hu
  obtain ⟨d,x,y,sf,_,div,point,ny,nx,back,_⟩ := fixed_twist_reduction hu S
  have pk : 0 < ∏ p ∈ S,p := Finset.prod_pos (fun p hp => (ps p hp).pos)
  have pm := contactSupport_pos S u
  have hdn : (d.natAbs:ℝ) ≤ ((∏ p ∈ S,p:ℕ):ℝ)*(contactSupport S u:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos pk pm) div
  have dp := pow_le_pow_left₀ (Nat.cast_nonneg d.natAbs : (0:ℝ)≤_) hdn 24
  rw [mul_pow] at dp
  have m1 : (1:ℝ) ≤ (contactSupport S u:ℝ)^24 := one_le_pow₀ (by exact_mod_cast pm)
  have log0 : 0 ≤ Real.log (1800:ℝ) := Real.log_nonneg (by norm_num)
  have bh := bound d x y sf ny nx point
  have ch := (changes_height x).2
  rw [back] at ch
  calc ratHeight u ≤ ratHeight x + Real.log 1800 := ch
       _ ≤ H*(((∏ p ∈ S,p:ℕ):ℝ)^24*(contactSupport S u:ℝ)^24) +
             Real.log 1800*(contactSupport S u:ℝ)^24 :=
         add_le_add (bh.trans (mul_le_mul_of_nonneg_left dp hH)) (le_mul_of_one_le_right log0 m1)
       _ = _ := by ring

theorem twists_of_contact (S : Finset ℕ) (small : ∀ p : ℕ, p.Prime → p ∉ S → 5<p)
    {A : ℝ} (hA : 0 ≤ A) (bound : ContactBound S A) : TwistBound (A+Real.log 1800) := by
  intro d x y sf ny nx point
  obtain ⟨hu,hx,_⟩ := inverse_parity sf ny nx point
  obtain ⟨e,k⟩ := inverse_kernel sf ny nx point
  have dvd := contact_dvd_kernel hu k S small
  have dpos := Int.natAbs_pos.mpr sf.ne_zero
  have md : (contactSupport S (120/(x-5)):ℝ) ≤ (d.natAbs:ℝ) := by exact_mod_cast Nat.le_of_dvd dpos dvd
  have dp := pow_le_pow_left₀ (Nat.cast_nonneg _ : (0:ℝ)≤_) md 24
  have d1 : (1:ℝ) ≤ (d.natAbs:ℝ)^24 := one_le_pow₀ (by exact_mod_cast dpos)
  have log0 : 0 ≤ Real.log (1800:ℝ) := Real.log_nonneg (by norm_num)
  have ch := (changes_height (120/(x-5))).1
  rw [hx] at ch
  calc ratHeight x ≤ ratHeight (120/(x-5)) + Real.log 1800 := ch
       _ ≤ A*(d.natAbs:ℝ)^24+Real.log 1800*(d.natAbs:ℝ)^24 :=
          add_le_add ((bound _ hu).trans (mul_le_mul_of_nonneg_left dp hA)) (le_mul_of_one_le_right log0 d1)
       _ = _ := by ring

#print axioms changes_height
#print axioms contact_dvd_kernel
#print axioms contact_of_twists
#print axioms twists_of_contact
end
end ZInQBlueprint.OddSupport
