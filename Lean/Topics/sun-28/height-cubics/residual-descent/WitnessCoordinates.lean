import IntrinsicHeight

/-! The discriminant support and height at one prescribed slope. -/
namespace Sun28.FiveDescent.ResidueField
open Sun28.Ordinary Sun28.FiveMarkUnits ZInQ.RouteK Height
noncomputable section

/-- For a primitive off-mark numerator and denominator, lift the actual slope
to the fixed sextic and identify the ramified primes and the rational height. -/
theorem exists_coordinates {A B : ℤ} (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    let t:=1-(B:ℚ)/A
    ∃ z v : Omega,z≠0 ∧ v≠0 ∧ z^2=algebraMap ℚ Omega t ∧
      v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) ∧
      (1-t)⁻¹=(A:ℚ)/B ∧ fieldPrimes z v=oldContactPrimes oldCutoff A B ∧
      logHeight₁ ((1-t)⁻¹)=pairLogHeight A B := by
  dsimp only
  obtain ⟨sd,se,x,y,nx,ny,pt,back⟩ := forward off
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (D A B:Omega) (by decide : 0<2)
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (E A B:Omega) (by decide : 0<2)
  let z:=r*algebraMap ℚ Omega x
  let v:=w*algebraMap ℚ Omega y
  have rn : r≠0 := by
    rintro rfl
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hr
    exact sd.ne_zero (by exact_mod_cast hr.symm)
  have wn : w≠0 := by
    rintro rfl
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hw
    exact se.ne_zero (by exact_mod_cast hw.symm)
  have rev : 1-(D A B:ℚ)*x^2=(B:ℚ)/A := by
    simpa only [parameter,inv_inv,inv_div] using congrArg (fun a : ℚ=>a⁻¹) back
  have t : 1-(B:ℚ)/A=(D A B:ℚ)*x^2 := by linarith only [rev]
  have inv : (1-(1-(B:ℚ)/A))⁻¹=(A:ℚ)/B := by rw [t];exact back
  have field : coords z v=coords r w := generated_coordinates r w nx ny
  have support : fieldPrimes z v=fieldPrimes r w := by
    unfold fieldPrimes
    rw [NumberField.discr_eq_discr_of_algEquiv _ (IntermediateField.equivOfEq field)]
  refine ⟨z,v,mul_ne_zero rn ((map_ne_zero (algebraMap ℚ Omega)).mpr nx),
    mul_ne_zero wn ((map_ne_zero (algebraMap ℚ Omega)).mpr ny),?_,
    (fixed_point_iff Omega _ _ r w (by simpa using hr) (by simpa using hw) x y).mp pt,
    inv,support.trans (marked_field_primes cop off hr hw).symm,?_⟩
  · simp [z,t,mul_pow,hr]
  · rw [inv,signed_height (rows off).2.1 cop]

/-- A version with the literal rational input: substitute any scalar or ordinary
slope directly and exclude precisely the five old marks. -/
theorem exists_coordinates_rat (s : ℚ) (off : ∀ i,oldForm i s.num s.den≠0) :
    let t:=1-s⁻¹
    ∃ z v : Omega,z≠0 ∧ v≠0 ∧ z^2=algebraMap ℚ Omega t ∧
      v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) ∧ (1-t)⁻¹=s ∧
      fieldPrimes z v=oldContactPrimes oldCutoff s.num s.den ∧
      logHeight₁ ((1-t)⁻¹)=logHeight₁ s := by
  have cop : Int.gcd s.num (s.den:ℤ)=1 := by simpa [Int.gcd] using s.reduced.gcd_eq_one
  have lift := exists_coordinates cop off
  dsimp only at lift ⊢
  have inv : ((s.den:ℤ):ℚ)/s.num=s⁻¹ := by
    rw [←inv_div,Int.cast_natCast,Rat.num_div_den]
  rw [inv,Int.cast_natCast,Rat.num_div_den] at lift
  obtain ⟨z,v,zn,vn,z2,v2,back,pr,_⟩:=lift
  exact ⟨z,v,zn,vn,z2,v2,back,pr,congrArg logHeight₁ back⟩

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.exists_coordinates
#print axioms Sun28.FiveDescent.ResidueField.exists_coordinates_rat
