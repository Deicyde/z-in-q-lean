import RootField

/-! Divisibility of the field discriminant forced by the square root of a squarefree integer. -/
namespace Sun28.FiveDescent.ResidueField
open NumberField IsDedekindDomain WithZero
open scoped NumberField
noncomputable section

/-- A prime appearing in a squarefree radicand ramifies in every number field
containing its square root. The proof uses the normalized valuation on an actual prime. -/
theorem prime_dvd_discr {L : Type*} [Field L] [NumberField L]
    {d : ℤ} (sf : Squarefree d) {u : L} (hu : u^2=(d:L))
    {p : ℕ} (pr : p.Prime) (div : p∣d.natAbs) : (p:ℤ)∣NumberField.discr L := by
  have pi : Prime (p:ℤ) := (Nat.prime_iff_prime_int.mp pr)
  let I : Ideal ℤ := Ideal.span {(p:ℤ)}
  have : I.IsPrime := (Ideal.span_singleton_prime pi.ne_zero).mpr pi
  have inzn : I≠⊥ := Ideal.span_singleton_eq_bot.not.mpr pi.ne_zero
  let v : HeightOneSpectrum ℤ := ⟨I,inferInstance,inzn⟩
  obtain ⟨⟨P,hP,above⟩⟩ := (inferInstance : Nonempty (I.primesOver (𝓞 L)))
  let : P.IsPrime := hP
  let : P.LiesOver I := above
  have pn : P≠⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot inzn P
  let w : HeightOneSpectrum (𝓞 L) := ⟨P,hP,pn⟩
  let : w.asIdeal.LiesOver v.asIdeal := above
  obtain ⟨k,hk⟩ : (p:ℤ)∣d := Int.natAbs_dvd_natAbs.mp (by simpa using div)
  have pk : ¬(p:ℤ)∣k := by
    rintro ⟨t,ht⟩
    have h : (p:ℤ)*(p:ℤ)∣d := ⟨t,by rw [hk,ht];ring⟩
    exact pi.not_isUnit (sf p h)
  have unit : v.intValuation k=1 := HeightOneSpectrum.intValuation_eq_one_iff.mpr
    (show k∉I by simpa only [I,Ideal.mem_span_singleton] using pk)
  have vd : v.intValuation d = exp (-1:ℤ) := by
    rw [hk,map_mul,unit,mul_one]
    exact v.intValuation_singleton pi.ne_zero rfl
  let iu : 𝓞 L := ⟨u,integral_root hu⟩
  have sq : iu^2=algebraMap ℤ (𝓞 L) d := Subtype.ext hu
  by_contra no
  have atP := (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) pi).mp no P hP
    ((Ideal.mem_of_liesOver P I _).mp (Ideal.mem_span_singleton_self _))
  have one : P.ramificationIdx ℤ=1 := Ideal.ramificationIdx_eq_one_iff.mpr atP
  have val := HeightOneSpectrum.intValuation_liesOver v w d
  rw [←sq,map_pow,vd,show w.asIdeal.ramificationIdx ℤ=1 from one,pow_one] at val
  have odd := congrArg WithZero.log val
  rw [WithZero.log_exp,WithZero.log_pow] at odd
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at odd
  omega

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.prime_dvd_discr
