import ScalarQuotient

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight
noncomputable section

def homogenized {R:Type*} [CommRing R] (a b:R) :=
  (2*a^2+3*b^2)*(a^2+b^2)*(a^2-1199*b^2)*(64*a^2+439*b^2)

private theorem local_table : ∀ a b Y:ZMod 9, homogenized a b=6*Y^2 →
    (a.val%3=0 ∧ b.val%3=0) := by decide

/-- Each primitive scalar value has its signed squarefree part over the integers. -/
theorem integral_point {x y:ℚ} {d:ℤ} (sf:Squarefree d) (yn:y≠0) (h:octic x=(d:ℚ)*y^2) :
    ∃Y:ℤ,homogenized x.num (x.den:ℤ)=d*Y^2 := by
  let H:=homogenized x.num (x.den:ℤ)
  have n : (x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  have val:(H:ℚ)=(d:ℚ)*(y*x.den^4)^2:=by
    have num:(x.num:ℚ)=x*x.den:=(div_eq_iff n).mp x.num_div_den
    dsimp [H,homogenized];push_cast
    rw [num]
    unfold octic at h
    linear_combination (x.den:ℚ)^8*h
  have yn':y*x.den^4≠0:=mul_ne_zero yn (pow_ne_zero 4 n)
  have hn:H≠0:=by
    intro z
    have z':(H:ℚ)=0:=by exact_mod_cast z
    exact (mul_ne_zero (by exact_mod_cast sf.ne_zero) (pow_ne_zero 2 yn')) (val.symm.trans z')
  have ids:ZInQ.RouteK.sqfInt H=d :=
    (ZInQ.RouteK.sqf_intCast _).symm.trans (ZInQ.RouteK.sqf_eq_of_eq_mul_sq sf yn' val)
  obtain ⟨_,c,_,e⟩:=ZInQ.RouteK.sqfInt_spec hn
  exact ⟨c,by simpa [ids] using e⟩

/-- Classes congruent to six modulo nine never occur. -/
theorem residue_six_excluded {x y:ℚ} {d:ℤ} (sf:Squarefree d) (yn:y≠0)
    (h:octic x=(d:ℚ)*y^2) : (d:ZMod 9)≠6 := by
  obtain ⟨Y,e⟩:=integral_point sf yn h
  have ev : homogenized (x.num:ZMod 9) (x.den:ZMod 9)=(d:ZMod 9)*(Y:ZMod 9)^2:=by
    simpa [homogenized] using congrArg (Int.castRingHom (ZMod 9)) e
  intro eqn
  rw [eqn] at ev
  obtain ⟨p,q⟩:=local_table _ _ _ ev
  have divN:(3:ℤ)∣x.num:=by
    have w:=ZMod.val_intCast (n:=9) x.num
    omega
  have divD:3∣x.den:=by
    rw [ZMod.val_natCast] at q
    omega
  have bad:3∣x.num.natAbs.gcd x.den:=Nat.dvd_gcd
    (by simpa using Int.natAbs_dvd_natAbs.mpr divN) divD
  rw [x.reduced.gcd_eq_one] at bad
  norm_num at bad

theorem actual_mod_nine (x:ℚ) : ((scalarClass x:ℤ):ZMod 9)≠6 := by
  obtain ⟨sf,_,yn,h⟩:=octic_twist x
  exact residue_six_excluded sf yn h

/-- If the genus-two quotient has only Weierstrass points then every point of the octic must lie over x=0. -/
theorem genus_two_reduction {d:ℚ} (dn:d≠0) (branch : ∀ z U:ℚ, U^2=d*quintic z → U=0)
    {x y:ℚ} (yn:y≠0) (h:octic x=d*y^2) : x=0 := by
  have zn:=branch _ _ (second_quotient h)
  rcases mul_eq_zero.mp zn with z|z
  · exact (mul_eq_zero.mp z).resolve_left dn
  · exact (yn z).elim

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.integral_point
#print axioms Sun28.ScalarQuotients.residue_six_excluded
#print axioms Sun28.ScalarQuotients.actual_mod_nine
#print axioms Sun28.ScalarQuotients.genus_two_reduction
