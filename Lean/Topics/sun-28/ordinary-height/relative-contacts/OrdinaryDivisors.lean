import MatchedRows

/-! Arithmetic on the two nonconstant scales of the actual nine-point certificate. -/
namespace Sun28.RelativeContacts
open ZInQ ZInQ.Mult Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.FixedPreparation Sun28.WitnessHeight Sun28.IndexHeights Height
noncomputable section
set_option maxRecDepth 12000

/-- The product of the coordinates costs precisely these denominator terms
when the two nonconstant rows each have one pair of matching marks. -/
def denominatorBudget (s : Fin 3→ℚ) (η : ℚ) : ℝ :=
  let B (i : Fin 3) := Real.log ((η.den:ℝ)*(s i).den^2)
  (3/4)*Real.log 3905573+B 1+B 2/2+10

theorem ratio_of_matched (s : Fin 3→ℚ) {η:ℚ} (en:η≠0) (unit:s 0=1)
    (one:Matched (s 1) η) (two:Matched (s 2) η) :
    ratioHeight (fun i=>(s i)^2*η)+10 ≤ denominatorBudget s η := by
  have h1:=matched_height en one
  have h2:=matched_height en two
  have r1 : ((s 1)^2*η)/((s 0)^2*η)=(s 1)^2 := by simp [unit,en]
  have r2 : ((s 2)^2*η)/((s 0)^2*η)=(s 2)^2 := by simp [unit,en]
  simp only [ratioHeight,r1,r2,logHeight₁_pow,Nat.cast_ofNat,denominatorBudget]
  linarith only [h1,h2]

/-- The sufficient condition contains two denominator heights and up to ten
square tests per nonconstant scale. The numerator of η is unrestricted. -/
theorem indices_of_matches (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (one:Matched (pointScale (nineAffine A).doubles fixedMultiplier 1) η)
    (two:Matched (pointScale (nineAffine A).doubles fixedMultiplier 2) η)
    (budget:denominatorBudget (pointScale (nineAffine A).doubles fixedMultiplier) η≤
      ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24) :
    OrdinaryIndices A η := by
  have en : η≠0 := by
    rintro rfl
    have bad := (accepted.scale_guard 0).1
    rw [mul_zero] at bad
    exact bad (by simp [marks])
  apply of_ratios A x η accepted
  exact (ratio_of_matched _ en (by simp [pointScale,scaleRoot]) one two).trans budget

theorem integral_adjacent_impossible (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (ed:η.den=1) (sd:(pointScale (nineAffine A).doubles fixedMultiplier 1).den=1) :
    let s:=pointScale (nineAffine A).doubles fixedMultiplier 1
    ¬ IsSquare (relativeForm s η (-1/2)*relativeForm s η (-1)) := by
  let s:=pointScale (nineAffine A).doubles fixedMultiplier 1
  let C:=rootProduct (nineAffine A).doubles fixedMultiplier
  have en : η≠0 := by
    rintro rfl
    have bad := (accepted.scale_guard 0).1
    rw [mul_zero] at bad
    exact bad (by simp [marks])
  change ¬ IsSquare (relativeForm s η (-1/2)*relativeForm s η (-1))
  intro pair
  have cap:=adjacent_num en pair
  change s.num^2≤((η.den:ℤ)*s.den^2)^2 at cap
  change s.den=1 at sd
  rw [ed,sd] at cap
  norm_num only at cap
  have neg : s.num≤1 := by nlinarith [sq_nonneg (s.num-1)]
  have ws : (s:ℝ)≤1 := by
    have h:=Rat.num_div_den s
    rw [sd] at h
    norm_num only [Nat.cast_one,div_one] at h
    exact_mod_cast (show s≤(1:ℚ) by rw [←h]; exact_mod_cast neg)
  have o1 : 0≤ordinary:=by unfold ordinary glazerConstant24;positivity
  have g : 0≤glazerConstant24:=by unfold glazerConstant24;positivity
  obtain ⟨a,e,_⟩:=extract_indices A anchor (K:=logConstant) o1 g
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  have coords : coordinateProduct a.n=C := rootProduct_eq e.represented
  have gem (σ : K0→+*ℝ) (bound:1<σ delta) : 1<σ C := by
    rw [←coords,coordinateProduct,map_prod]
    have live (i:Fin 4) : a.n i≠0 := by obtain ⟨k,hk⟩:=e.odd i;omega
    simp only [Fin.prod_univ_four]
    have big (i:Fin 4):1<σ (indexX (a.n i)):=
      bound.trans_le (generator_real_lower σ bound.le (live i))
    have merge {a b:ℝ} (av:1<a) (bv:1<b) : 1<a*b := by
      nlinarith only [av,bv,mul_pos (sub_pos.mpr av) (sub_pos.mpr bv)]
    exact merge (merge (merge (big 0) (big 1)) (big 2)) (big 3)
  have lowp : 1<K0.embPlus delta := by
    rw [embPlus_delta];linarith [sqrt_two_lt_two]
  have lowm : 1<K0.embMinus delta := by
    rw [embMinus_delta];linarith [Real.sqrt_nonneg (2:ℝ)]
  have pos:=gem K0.embPlus lowp
  have neg:=gem K0.embMinus lowm
  change (C.re:ℝ)≤1 at ws
  rw [K0.embPlus_apply] at pos
  rw [K0.embMinus_apply] at neg
  linarith

/-- After specializing the three scales, the entire denominator cost is the
height of the input denominator and the product of the two coefficient denominators. -/
theorem actual_denominator_formula (C : K0) (η : ℚ) :
    denominatorBudget (scaleRoot C.re C.im) η =
      (3/4)*Real.log 3905573+(3/2)*Real.log η.den+
        2*Real.log ((C.re.den:ℝ)*C.im.den)+10 := by
  have addDen : (1+C.im^2).den=C.im.den^2 := by
    exact (show (1+C.im^2).den=(C.im^2).den by simpa only [Int.cast_one] using Rat.intCast_add_den 1 (C.im^2)).trans (Rat.den_pow C.im 2)
  have ea : (η.den:ℝ)≠0 := by exact_mod_cast η.den_nz
  have ca : (C.re.den:ℝ)≠0 := by exact_mod_cast C.re.den_nz
  have cb : (C.im.den:ℝ)≠0 := by exact_mod_cast C.im.den_nz
  change (3/4)*Real.log 3905573+Real.log ((η.den:ℝ)*(C.re.den:ℝ)^2)+
    Real.log ((η.den:ℝ)*((1+C.im^2).den:ℝ)^2)/2+10=_
  rw [addDen,Nat.cast_pow,Real.log_mul ea (pow_ne_zero _ ca),Real.log_mul ea (pow_ne_zero _ (pow_ne_zero _ cb)),
    Real.log_mul ca cb,Real.log_pow,Real.log_pow,Real.log_pow]
  ring

/-- At the original cutoff the exact twelve squareclasses on the actual points
select precisely the primes in both ordinary index divisibilities. -/
theorem accepted_support {p : ℕ} [hp : Fact p.Prime] (out:p∉oldCutoff)
    (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) :
    p∈contactUnion oldCutoff (slope (nineAffine A).doubles η) ↔
      ∃ i a, a∈marks ∧ a≠0 ∧ Odd (padicValRat p
        (relativeForm (pointScale (nineAffine A).doubles fixedMultiplier i) η a)) := by
  have outside:=commonCutoff_outside anchor_nonzero (gamma:ℚ) smallMultipliers smallMultipliers
  rw [fixed_cutoff] at outside
  have en : η≠0 := by
    rintro rfl
    have bad := (accepted.scale_guard 0).1
    rw [mul_zero] at bad
    exact bad (by simp [marks])
  apply union_iff_odd_relative out (outside p hp.out out).2.2.1 _ en
  · exact fun i => (accepted.scale_guard i).2.2
  · exact fun i => (accepted.scale_guard i).1

end
end Sun28.RelativeContacts
#print axioms Sun28.RelativeContacts.ratio_of_matched
#print axioms Sun28.RelativeContacts.indices_of_matches
#print axioms Sun28.RelativeContacts.integral_adjacent_impossible
#print axioms Sun28.RelativeContacts.actual_denominator_formula
#print axioms Sun28.RelativeContacts.accepted_support
