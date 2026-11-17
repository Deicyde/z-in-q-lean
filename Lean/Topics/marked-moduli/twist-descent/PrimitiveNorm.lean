import CubicForms

/-! The cubic coordinates are primitive after a factor of eight at two. -/
namespace ZInQBlueprint.TwistDescent

private theorem odd_tables : ∀ u v : ZMod 16, u^8=1 → v^8=1 →
    u*(u^2-9*v^2)*2=0 ∧ v*(u^2-v^2)*2=0 ∧
    (u^2+3*v^2)*4=0 ∧ ¬(u*(u^2-9*v^2)=0 ∧ v*(u^2-v^2)=0) := by decide

private theorem odd_power (a : ℤ) (ha : ¬2 ∣ a) : (a:ZMod 16)^8=1 := by
  have table : ∀ u : ZMod 16, ¬(u*8=0) → u^8=1 := by decide
  apply table
  intro h
  have d : (16:ℤ) ∣ a*8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (by simpa using h)
  exact ha (by omega)

private theorem normalization_at_two {a b : ℤ} (ha : ¬2 ∣ a) (hb : ¬2 ∣ b) :
    8 ∣ realCubic a b ∧ 8 ∣ imaginaryCubic a b ∧ 4 ∣ quadraticNorm a b ∧
    ¬(16 ∣ realCubic a b ∧ 16 ∣ imaginaryCubic a b) := by
  obtain ⟨A,B,C,no⟩ := odd_tables (a:ZMod 16) (b:ZMod 16) (odd_power a ha) (odd_power b hb)
  have a' : (16:ℤ) ∣ realCubic a b*2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (by simpa [realCubic] using A)
  have b' : (16:ℤ) ∣ imaginaryCubic a b*2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (by simpa [imaginaryCubic] using B)
  have c' : (16:ℤ) ∣ quadraticNorm a b*4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp (by simpa [quadraticNorm] using C)
  refine ⟨by omega,by omega,by omega,?_⟩
  rintro ⟨hA,hB⟩
  apply no
  exact ⟨by simpa [realCubic] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr hA,
    by simpa [imaginaryCubic] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr hB⟩

private theorem opposite_at_two {a b : ℤ} (hab : a.natAbs.Coprime b.natAbs)
    (h : ¬(¬2 ∣ a ∧ ¬2 ∣ b)) : ¬(2 ∣ realCubic a b ∧ 2 ∣ imaginaryCubic a b) := by
  rintro ⟨hA,hB⟩
  have za := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hA
  have zb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hB
  simp only [realCubic,imaginaryCubic,Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat] at za zb
  have table : ∀ u v : ZMod 2, u*(u^2-9*v^2)=0 → v*(u^2-v^2)=0 → u=v := by decide
  have eq := table _ _ za zb
  have ha : (2:ℤ) ∣ a ↔ (2:ℤ) ∣ b := by
    have ha := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2)
    have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2)
    exact ha.symm.trans (eq ▸ hb)
  have both : (2:ℤ) ∣ a ∧ (2:ℤ) ∣ b := by tauto
  apply (Nat.Prime.not_coprime_iff_dvd.mpr ?_) hab
  exact ⟨2,by decide,Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr both.1),
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr both.2)⟩

private theorem primitive_cubics {a b P Q g : ℤ} (hab : a.natAbs.Coprime b.natAbs)
    (hP : g*P=realCubic a b) (hQ : g*Q=imaginaryCubic a b)
    (two : ¬(2 ∣ P ∧ 2 ∣ Q)) : P.natAbs.Coprime Q.natAbs := by
  by_contra h
  obtain ⟨p,prime,pP,pQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have iP : (p:ℤ) ∣ P := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr pP)
  have iQ : (p:ℤ) ∣ Q := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr pQ)
  have h2 := prime_dvd_both hab prime (hP ▸ dvd_mul_of_dvd_right iP g)
    (hQ ▸ dvd_mul_of_dvd_right iQ g)
  subst p
  exact two ⟨iP,iQ⟩

/-- A factor of 2 in the quadratic coordinates contributes factors 8,8,4.
The normalized product is primitive in both parity cases. -/
theorem primitive_norm (a b : ℤ) (hab : a.natAbs.Coprime b.natAbs) :
    ∃ k P Q T : ℤ, (k=1 ∨ k=2) ∧ k^3*P=realCubic a b ∧
      k^3*Q=imaginaryCubic a b ∧ k^2*T=quadraticNorm a b ∧
      P.natAbs.Coprime Q.natAbs ∧ P^2+27*Q^2=T^3 := by
  by_cases h : ¬2 ∣ a ∧ ¬2 ∣ b
  · obtain ⟨⟨P,hP⟩,⟨Q,hQ⟩,⟨T,hT⟩,no⟩ := normalization_at_two h.1 h.2
    have cop := primitive_cubics hab hP.symm hQ.symm (by
      rintro ⟨t,s⟩
      exact no ⟨by rw [hP]; omega,by rw [hQ]; omega⟩)
    refine ⟨2,P,Q,T,Or.inr rfl,by simpa using hP.symm,by simpa using hQ.symm,
      by simpa using hT.symm,cop,?_⟩
    have id := cubic_identity a b
    rw [hP,hQ,hT] at id
    nlinarith only [id]
  · refine ⟨1,realCubic a b,imaginaryCubic a b,quadraticNorm a b,Or.inl rfl,
      by simp,by simp,by simp,primitive_cubics (g:=1) hab (by simp) (by simp) (opposite_at_two hab h),
      cubic_identity a b⟩

#print axioms primitive_norm
end ZInQBlueprint.TwistDescent
