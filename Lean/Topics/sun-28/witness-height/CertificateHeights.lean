import UnionSupport
import IntegerProjection

/-! Two pointwise height inequalities suffice for a rational certificate. -/
namespace Sun28.WitnessHeight
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.FixedPreparation Sun28.MinimalConductors Height
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000

/-- The primitive coordinates used by the ordinary detector before its fractional linear change. -/
def sourcePair (t : ℚ) : ℤ × ℤ := (2*t.num+t.den,t.num)

def slope (w : NinePoints) (η : ℚ) (j : Fin 3) : ℚ :=
  (pointScale w fixedMultiplier j)^2*η

theorem source_primitive (t : ℚ) : Int.gcd (sourcePair t).1 (sourcePair t).2=1 := by
  rw [sourcePair,primitive_phi]
  simpa [Int.gcd] using t.reduced.gcd_eq_one

theorem source_off (t : ℚ) (off : t∉marks) : ∀ i, oldForm i (sourcePair t).1 (sourcePair t).2≠0 := by
  intro i
  have different : t≠transportedMark i := fun e => off (e ▸ (marks_image _).mpr ⟨i,rfl⟩)
  have live : contactForm t (transportedMark i)≠0 := by
    intro z
    apply different
    have e : t.num*((transportedMark i).den:ℤ)=(transportedMark i).num*(t.den:ℤ) := sub_eq_zero.mp z
    rw [←Rat.num_div_den t,←Rat.num_div_den (transportedMark i)]
    apply (div_eq_div_iff (by exact_mod_cast t.den_nz) (by exact_mod_cast (transportedMark i).den_nz)).mpr
    exact_mod_cast e
  change oldForm i (2*t.num+t.den) t.num≠0
  rw [old_form_pullback,reduced_forms]
  split_ifs <;> simpa using live

theorem ordinary_transport (t : ℚ) (bound : target (sourcePair t).1 (sourcePair t).2) :
    logHeight₁ t≤fiveHeightConstant oldCutoff*(∏ p∈contactPrimes oldCutoff t,(p:ℝ))^24 := by
  change pairLogHeight (2*t.num+t.den) t.num≤
    glazerConstant24*(∏ p∈oldContactPrimes oldCutoff (2*t.num+t.den) t.num,(p:ℝ))^24 at bound
  rw [transported_contact_primes] at bound
  let R : ℝ := ∏ p∈contactPrimes oldCutoff t,(p:ℝ)
  have r1 : 1≤R := by
    dsimp [R]; rw [←Nat.cast_prod]; exact_mod_cast Nat.succ_le_of_lt (radical_pos oldCutoff t)
  have plus : Real.log 3≤Real.log 3*R^24 := by
    simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ r1 (n:=24)) (Real.log_nonneg (by norm_num : (1:ℝ)≤3))
  have coeff : glazerConstant24+Real.log 3 ≤ fiveHeightConstant oldCutoff := by
    simp [fiveHeightConstant,extraPrimes]
  rw [logHeight_reduced_pair]
  have move:=logHeight_phi t.num t.den (Or.inr (by exact_mod_cast t.den_nz))
  change pairLogHeight t.num t.den≤fiveHeightConstant oldCutoff*R^24
  calc
    _ ≤ (glazerConstant24+Real.log 3)*R^24 := by
      change pairLogHeight (2*t.num+t.den) t.num ≤ glazerConstant24*R^24 at bound
      linarith only [move,bound,plus]
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff (by positivity)

theorem scalar_transport (x : ℚ) (bound : target (beta x).num (beta x).den) :
    logHeight₁ (beta x)≤glazerConstant24*(oldRadical oldCutoff (beta x):ℝ)^24 := by
  rw [logHeight_reduced_pair]
  simpa only [target,oldRadical,Nat.cast_prod] using bound

/-- The bound at the largest ordinary slope can use all three sets of contact primes. -/
def unionHeight (t : Fin 3 → ℚ) (j : Fin 3) : Prop :=
  logHeight₁ (t j) ≤ fiveHeightConstant oldCutoff*(unionRadical oldCutoff t:ℝ)^24

theorem ordinary_to_union (t : Fin 3 → ℚ) (j : Fin 3)
    (bound : target (sourcePair (t j)).1 (sourcePair (t j)).2) : unionHeight t j := by
  have smaller := ordinary_transport (t j) bound
  have inclusion : (contactRadical oldCutoff (t j):ℝ) ≤ (unionRadical oldCutoff t:ℝ) := by
    exact_mod_cast member_radical_le oldCutoff t j
  rw [←Nat.cast_prod] at smaller
  apply smaller.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) inclusion 24)
    (zero_le_one.trans (le_max_left _ _))

/-- The attained three-row conductor gives a direct computable test with the union bound. -/
def conductorHeight (t : Fin 3 → ℚ) (j : Fin 3) : Prop :=
  let v := sourcePair (t j)
  vonKanelBound (best v.1 v.2)+Real.log 3 ≤
    fiveHeightConstant oldCutoff*(unionRadical oldCutoff t:ℝ)^24

theorem union_of_conductor (units : Sun28.FiveMarkUnits.PublishedCorollary72)
    (t : Fin 3 → ℚ) (j : Fin 3) (off : t j∉marks) (h : conductorHeight t j) : unionHeight t j := by
  have unitBound := attained_height units (source_primitive (t j)) (source_off (t j) off)
  have move := logHeight_phi (t j).num (t j).den (Or.inr (by exact_mod_cast (t j).den_nz))
  unfold unionHeight
  rw [logHeight_reduced_pair]
  apply LE.le.trans _ h
  change pairLogHeight (2*(t j).num+(t j).den) (t j).num ≤ _ at unitBound
  linarith only [move,unitBound]

/-- A bound at the scalar input and a bound with the union radical at a largest
ordinary slope imply integrality of an accepted input. -/
theorem integral_of_union_height (A : Fin 9 → AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (j : Fin 3) (largest : ∀ i, logHeight₁ (slope (nineAffine A).doubles η i)≤
      logHeight₁ (slope (nineAffine A).doubles η j))
    (ordinaryHeight : unionHeight (slope (nineAffine A).doubles η) j)
    (scalarHeight : target (beta x).num (beta x).den) :
    ∃ k : ℤ, x=(k:ℚ) := by
  let w := (nineAffine A).doubles
  let M := fixedMultiplier
  let C := rootProduct w M
  let t := slope w η
  have gl : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  have o1 : 1≤ordinary := by
    have f := le_max_left (1:ℝ) (glazerConstant24*(∏ p∈extraPrimes oldCutoff oldCutoff,(p:ℝ))^24+Real.log 3)
    change 1≤fiveHeightConstant oldCutoff at f
    rw [←fixed_coefficients.2]
    unfold ordinaryCoefficient ordinaryConstant
    linarith
  obtain ⟨a,e,_⟩ := extract_indices A anchor (K:=logConstant) (zero_le_one.trans o1) gl
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  change Consequences w M anchor a at e
  have en : η≠0 := by
    rintro rfl
    have z := (accepted.scale_guard 0).1
    rw [mul_zero] at z
    exact z (by simp [marks])
  have coords : coordinateProduct a.n=C := rootProduct_eq e.represented
  have scale : ∀ H : ℝ, 1≤H → (∀ i,logHeight₁ (t i)≤H) → (indexSize a.n)^2≤(3/2)*H+10 := by
    change ∀ H : ℝ, 1≤H → (∀ i,logHeight₁ ((scaleRoot C.re C.im i)^2*η)≤H) → _
    rw [←coords]
    exact three_scales a.n e.odd η en
  have outside := commonCutoff_outside anchor_nonzero (gamma:ℚ) smallMultipliers smallMultipliers
  rw [fixed_cutoff] at outside
  have tests : ∀ i, let s:=pointScale w M i
      testTrace sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)≠0 ∧
      polePredicate smallMultipliers (poleArgument sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)) :=
    fun i => (ordinaryAccepted_iff e ..).1 (accepted.ordinary i)
  have prod := three_marked_products sqrt2_sq conjugation conjugation_nontrivial anchor a.h a.n a.m
    (beta x) (pointScale w M) t smallMultipliers oldCutoff e.h_nonzero e.base_nonzero outside
    (ShortFormal.ordinaryCharts oldCutoff K0) accepted.scale_guard tests
  obtain ⟨ord,num⟩ := ordinary_of_union oldCutoff t a.n (beta x)
    (le_max_left _ _) (by norm_num : (0:ℝ)≤3/2) (by norm_num : (0:ℝ)≤10)
    scale j largest ordinaryHeight prod
  change lucas (a.n 1) (a.n 2) (a.n 3)≠0 → (indexSize a.n)^2≤ordinaryCoefficient oldCutoff*_ at ord
  change beta x ≠ (a.n 0:ℚ) → (indexSize a.n)^2≤ordinaryCoefficient oldCutoff*_ at num
  rw [fixed_coefficients.2] at ord num
  have enlar : exceptional (gamma:ℚ) smallMultipliers ⊆ oldCutoff := by
    rw [←fixed_cutoff]
    exact fun _ h => Finset.mem_union_left _ h
  have tree := tree_of_points e _ _ _ _ accepted.scalar
  have dv := scalar_product48_at_cutoff sqrt2_sq a.h (a.n 1) x gamma denominator smallMultipliers oldCutoff
    enlar e.h_nonzero (by exact_mod_cast gamma_positive.ne') (ShortFormal.ordinaryCharts oldCutoff K0) tree
  have nz : a.n 1-1≠0 := fun z => scalar_point_guard e (by rw [z,zero_zsmul])
  have hs := (scalar_transport x scalarHeight).trans (mul_le_mul_of_nonneg_left (sqrt_of_power_dvd nz dv) gl)
  have physical : logHeight₁ (beta x)≤glazerConstant24*Real.sqrt (scalarStep a.n:ℝ) := by
    simpa only [scalarStep,Nat.cast_natAbs,Int.cast_abs] using hs
  apply (index_soundness x a.n a.q e.q_nonzero e.z_nonzero o1 gl e.anchor ord _ physical).2
  exact fun ne => ordinary_log_height (beta x) (a.n 0) (one_le_indexSize a.n) (abs_first_le_indexSize a.n)
    o1 ne (num ne)

theorem integral_of_two_heights (A : Fin 9 → AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (j : Fin 3) (largest : ∀ i, logHeight₁ (slope (nineAffine A).doubles η i)≤
      logHeight₁ (slope (nineAffine A).doubles η j))
    (ordinaryHeight : let v:=sourcePair (slope (nineAffine A).doubles η j); target v.1 v.2)
    (scalarHeight : target (beta x).num (beta x).den) : ∃ k : ℤ, x=(k:ℚ) :=
  integral_of_union_height A x η accepted j largest (ordinary_to_union _ j ordinaryHeight) scalarHeight

end
end Sun28.WitnessHeight

#print axioms Sun28.WitnessHeight.source_primitive
#print axioms Sun28.WitnessHeight.source_off
#print axioms Sun28.WitnessHeight.ordinary_transport
#print axioms Sun28.WitnessHeight.scalar_transport
#print axioms Sun28.WitnessHeight.integral_of_two_heights
#print axioms Sun28.WitnessHeight.ordinary_to_union
#print axioms Sun28.WitnessHeight.union_of_conductor
#print axioms Sun28.WitnessHeight.integral_of_union_height
