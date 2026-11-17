import NegativeDiscs

namespace Sun28.ConicNegative
noncomputable section

/-- The primitive parameter preserves the original s, so these two congruences apply to
the reduced numerator and denominator of the marked scalar rather than just to its cover. -/
theorem marked_residues {s:ℚ} (h:component s) (f:rationalFactors s) :
    ∀m:ℕ, m=17 ∨ m=19 →
      ¬(m:ℤ) ∣ (s.den:ℤ) ∧ (m:ℤ)∣s.num-4*(s.den:ℤ) := by
  obtain ⟨a,b,_,_,e,loc,_⟩:=certified_discs h f
  let D:ℤ:=120*width a b^2
  let L:ℤ:=numerator a b
  have dc:s*(D:ℚ)=(L:ℚ) := by
    dsimp [D,L,numerator,width,H] at *
    push_cast
    linear_combination e
  have hden : (s.den:ℚ)≠0 := by exact_mod_cast s.den_nz
  have rep : (s.num:ℚ)=s*s.den := (div_eq_iff hden).mp s.num_div_den
  have mulid : s.num*D=(s.den:ℤ)*L := by
    exact_mod_cast (show (s.num:ℚ)*(D:ℚ)=(s.den:ℚ)*(L:ℚ) by rw [rep,←dc]; ring)
  intro m hm
  have pp:m.Prime:=by rcases hm with rfl|rfl <;> decide
  have ip : Prime (m:ℤ) := Nat.prime_iff_prime_int.mp pp
  obtain ⟨nz,ld⟩:=loc m hm
  have dn : ¬(m:ℤ)∣D := by intro v;exact nz (Int.emod_eq_zero_of_dvd v)
  constructor
  · intro dv
    have v:(m:ℤ)∣s.num*D := mulid.symm ▸ dvd_mul_of_dvd_left dv _
    have both:=ip.dvd_mul.mp v
    have pn:(m:ℤ)∣s.num:=both.resolve_right dn
    exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr pn)
      (by simpa using Int.natAbs_dvd_natAbs.mpr dv) s.reduced
  · have rel :(s.num-4*(s.den:ℤ))*D=(s.den:ℤ)*(L-4*D) := by linear_combination mulid
    have ld':(m:ℤ)∣L-4*D :=by convert ld using 1;dsimp [L,D];ring
    exact (ip.dvd_mul.mp (rel ▸ dvd_mul_of_dvd_right ld' _)).resolve_right dn

private theorem units17 : (784:ZMod 17)≠0 ∧ (36:ZMod 17)≠0 := by decide
private theorem units19 : (784:ZMod 19)≠0 ∧ (36:ZMod 19)≠0 := by decide

/-- The original marked equation then fixes the x-discs at both primes. -/
theorem original_residues {s x:ℚ} (h:component s) (f:rationalFactors s)
    (marked : 343*(15+5*s)^2-439*(1+5*s)^2=(8*x*(1+5*s))^2) :
    ∀m:ℕ, m=17 ∨ m=19 →
      ¬(m:ℤ)∣(x.den:ℤ) ∧ (m:ℤ)∣36*x.num^2-289*(x.den:ℤ)^2 := by
  have sd : (s.den:ℚ)≠0 := by exact_mod_cast s.den_nz
  have xd : (x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  have sr : (s.num:ℚ)=s*s.den :=(div_eq_iff sd).mp s.num_div_den
  have xr : (x.num:ℚ)=x*x.den :=(div_eq_iff xd).mp x.num_div_den
  have clear : (x.den:ℤ)^2*(343*(15*(s.den:ℤ)+5*s.num)^2-439*((s.den:ℤ)+5*s.num)^2)=
      (8*x.num*((s.den:ℤ)+5*s.num))^2 := by
    exact_mod_cast (show (x.den:ℚ)^2*(343*(15*(s.den:ℚ)+5*(s.num:ℚ))^2-439*((s.den:ℚ)+5*(s.num:ℚ))^2)=
      (8*(x.num:ℚ)*((s.den:ℚ)+5*(s.num:ℚ)))^2 by
      rw [sr,xr];linear_combination (x.den:ℚ)^2*(s.den:ℚ)^2*marked)
  intro m hm
  have pp : m.Prime:=by rcases hm with rfl|rfl <;> decide
  let _ : Fact m.Prime:=⟨pp⟩
  obtain ⟨sunit,sval⟩:=marked_residues h f m hm
  have unit : (s.den:ZMod m)≠0 := by
    intro z
    exact sunit ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by simpa using z))
  have sn : (s.num:ZMod m)=4*(s.den:ZMod m) := by
    have z:((s.num-4*(s.den:ℤ):ℤ):ZMod m)=0:=(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr sval
    push_cast at z;exact sub_eq_zero.mp z
  have z:=congrArg (Int.castRingHom (ZMod m)) clear
  simp only [map_pow,map_mul,map_sub,map_add,map_ofNat,Int.coe_castRingHom,Int.cast_natCast] at z
  rw [sn] at z
  have coeff:(784:ZMod m)≠0:=by
    rcases hm with rfl|rfl
    · exact units17.1
    · exact units19.1
  have ze : (784:ZMod m)*(s.den:ZMod m)^2 *
        (36*(x.num:ZMod m)^2-289*(x.den:ZMod m)^2)=0 := by linear_combination -z
  have target:= (mul_eq_zero.mp ze).resolve_left (mul_ne_zero coeff (pow_ne_zero _ unit))
  have result : (m:ℤ)∣36*x.num^2-289*(x.den:ℤ)^2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by push_cast; exact target)
  refine ⟨?_,result⟩
  intro dv
  have dd:(x.den:ZMod m)=0:=by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr dv
  have cn:(36:ZMod m)≠0:=by
    rcases hm with rfl|rfl
    · exact units17.2
    · exact units19.2
  rw [dd] at target
  simp [cn] at target
  have vn:((m:ℤ)∣x.num):=(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp target
  exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr vn)
    (by simpa using Int.natAbs_dvd_natAbs.mpr dv) x.reduced

end
end Sun28.ConicNegative
#print axioms Sun28.ConicNegative.marked_residues
#print axioms Sun28.ConicNegative.original_residues
