import SimplePrimeRoots

namespace Sun28.TwistPrimes

/-- The two positive factors of the integral quartic are coprime. -/
theorem factors_coprime {β k : ℕ} (hk : β<k^2) (bk : β.Coprime k)
    (six : 6∣k) : (k^2-β).Coprime (9*k^2-β) := by
  by_contra nd
  obtain ⟨p,pp,d1,d2⟩ := Nat.Prime.not_coprime_iff_dvd.mp nd
  let : Fact p.Prime := ⟨pp⟩
  have nine : β≤9*k^2 := by omega
  have u := (ZMod.natCast_eq_zero_iff _ _).mpr d1
  have v := (ZMod.natCast_eq_zero_iff _ _).mpr d2
  rw [Nat.cast_sub hk.le,Nat.cast_pow] at u
  rw [Nat.cast_sub nine,Nat.cast_mul,Nat.cast_pow] at v
  have bad : p∣8*k^2 := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    linear_combination v-u)
  have dk : p∣k := by
    rcases pp.dvd_mul.mp bad with small|power
    · have e : p∣2^3 := small
      exact ((pp.dvd_of_dvd_pow e).trans (by decide : 2∣6)).trans six
    · exact pp.dvd_of_dvd_pow power
  have b : (β:ZMod p)=0 := by
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr dk] at u
    simpa using u
  exact pp.not_dvd_one (bk ▸ Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ _).mp b) dk)

private theorem square_of_coprime_product {a b h : ℕ} (cp : a.Coprime b)
    (nz : a*b≠0) (eq : a*b=h^2) : IsSquare b := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p pp
  by_cases db : p∣b
  · have da : ¬p∣a := fun d=>pp.not_dvd_one (cp ▸ Nat.dvd_gcd d db)
    have z := congrArg (fun n : ℕ=> n.factorization p) eq
    simp only [Nat.factorization_mul (left_ne_zero_of_mul nz) (right_ne_zero_of_mul nz),
      Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd da,zero_add,Nat.factorization_pow,
      Finsupp.smul_apply,smul_eq_mul] at z
    exact ⟨h.factorization p,by omega⟩
  · simp [Nat.factorization_eq_zero_of_not_dvd db]

private theorem square_alternative {a b θ h : ℕ} (cp : a.Coprime b) (pt : θ.Prime)
    (nz : a*b≠0) (eq : a*b=θ*h^2) : IsSquare a ∨ IsSquare b := by
  have div : θ∣a*b := eq ▸ dvd_mul_right _ _
  rcases pt.dvd_mul.mp div with da | db
  · obtain ⟨t,et⟩ := da
    have c : t.Coprime b := cp.of_dvd_left (et ▸ dvd_mul_left _ _)
    have e : t*b=h^2 := Nat.eq_of_mul_eq_mul_left pt.pos (by rw [←eq,et,Nat.mul_assoc])
    have z : t*b≠0 := by intro z; apply nz; rw [et,Nat.mul_assoc,z,mul_zero]
    exact Or.inr (square_of_coprime_product c z e)
  · obtain ⟨t,et⟩ := db
    have c : t.Coprime a := cp.symm.of_dvd_left (et ▸ dvd_mul_left _ _)
    have swap : b*a=θ*h^2 := (Nat.mul_comm b a).trans eq
    have e : t*a=h^2 := Nat.eq_of_mul_eq_mul_left pt.pos (by rw [←swap,et,Nat.mul_assoc])
    have z : t*a≠0 := by intro z; apply nz; rw [Nat.mul_comm a b,et,Nat.mul_assoc,z,mul_zero]
    exact Or.inl (square_of_coprime_product c z e)

private theorem index_bound_of_square {β m : ℕ} (hb : 0<β) (hm : β<m^2)
    (s : IsSquare (m^2-β)) : 2*m≤β+1 := by
  obtain ⟨v,e⟩ := s
  have eq : m^2=β+v^2 := by rw [pow_two v,←e]; omega
  have less : v<m := by
    by_contra! bad
    have h := Nat.pow_le_pow_left bad 2
    omega
  have h := Nat.pow_le_pow_left (show v+1≤m by omega) 2
  have Q : v≤m-1 := by omega
  have mono := Nat.pow_le_pow_left Q 2
  have pred : m-1+1=m := Nat.sub_add_cancel (by omega)
  nlinarith [show (m-1+1)^2=m^2 by rw [pred]]

/-- Prime outputs are restricted to finitely many integer indices on each
β-fibre. The statement does not restrict rational indices. -/
theorem prime_index_bound {β k θ h : ℕ} (hb : 0<β) (hk : β<k^2) (bk : β.Coprime k)
    (six : 6∣k) (pt : θ.Prime) (eq : (k^2-β)*(9*k^2-β)=θ*h^2) : 2*k≤β+1 := by
  have nine : β<9*k^2 := by omega
  have nz : (k^2-β)*(9*k^2-β)≠0 := (Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.sub_pos_of_lt nine)).ne'
  rcases square_alternative (factors_coprime hk bk six) pt nz eq with first | second
  · exact index_bound_of_square hb hk first
  · have e : (3*k)^2=9*k^2 := by ring
    have z := index_bound_of_square (m:=3*k) hb (e ▸ nine) (e ▸ second)
    omega

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.factors_coprime
#print axioms Sun28.TwistPrimes.prime_index_bound
