import InertScalar

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight
noncomputable section

/-- Each odd prime factor of a represented twist splits at least one of the four quadratic factors. -/
theorem splitting_at_prime {x y : ℚ} {d : ℤ} (sf : Squarefree d) (live : y≠0)
    (curve : octic x=(d:ℚ)*y^2) {p : ℕ} (pp : p.Prime) (odd : 2 < p) (pd : p∣d.natAbs) :
    IsSquare (-6:ZMod p) ∨ IsSquare (-1:ZMod p) ∨ IsSquare (1199:ZMod p) ∨ IsSquare (-439:ZMod p) := by
  let _ : Fact p.Prime := ⟨pp⟩
  obtain ⟨Y,e⟩ := integral_point sf live curve
  let a : ZMod p := x.num
  let b : ZMod p := (x.den:ℤ)
  have prim : ¬ (a=0 ∧ b=0) := by
    rintro ⟨pa,pb⟩
    have da := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp pa
    have db := (ZMod.intCast_zmod_eq_zero_iff_dvd (x.den:ℤ) p).mp pb
    exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr da)
      (by simpa using Int.natAbs_dvd_natAbs.mpr db)) x.reduced
  have two : (2:ZMod p)≠0 := by
    intro q
    have h : (p:ℤ)∣2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using q)
    have k : p∣2 := by exact_mod_cast h
    exact (not_le_of_gt odd) (Nat.le_of_dvd (by decide) k)
  have sixty : (64:ZMod p)≠0 := by
    rw [show (64:ZMod p)=2^6 by norm_num]
    exact pow_ne_zero _ two
  have de : (d:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr
    (Int.natAbs_dvd_natAbs.mp (by simpa using pd))
  have prod : (2*a^2+3*b^2)*(a^2+b^2)*(a^2-1199*b^2)*(64*a^2+439*b^2)=0 := by
    have v := congrArg (fun k : ℤ => (k:ZMod p)) e
    simpa only [homogenized,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      Int.cast_ofNat,de,zero_mul,a,b] using v
  by_cases bz : b=0
  · have az : a≠0 := fun h=>prim ⟨h,bz⟩
    exfalso
    simp [bz,az,sixty,two] at prod
  · simp only [mul_eq_zero] at prod
    rcases prod with ((h|h)|h)|h
    · left
      refine ⟨2*a/b,?_⟩
      field_simp;linear_combination -2*h
    · right;left
      refine ⟨a/b,?_⟩
      field_simp;linear_combination -h
    · right;right;left
      refine ⟨a/b,?_⟩
      field_simp;linear_combination -h
    · right;right;right
      refine ⟨8*a/b,?_⟩
      field_simp;linear_combination -h

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.splitting_at_prime
