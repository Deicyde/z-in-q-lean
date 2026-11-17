import ScalarOctic

namespace Sun28.ScalarQuotients
noncomputable section

/-- The normalized third division polynomial, homogenized. -/
def psiThree {R:Type*} [CommRing R] (a b:R) : R :=
  3*a^4-116*a^3*b-576*a^2*b^2-9216*b^4

private theorem zero_mod_eleven : ∀ a b:ZMod 11, psiThree a b=0 → a=0 ∧ b=0 := by decide

theorem no_three_root (r:ℚ) : psiThree r 1≠0 := by
  intro z
  have dn:(r.den:ℚ)≠0:=by exact_mod_cast r.den_nz
  have eqn:psiThree r.num (r.den:ℤ)=0:=by
    have qr:psiThree (r.num:ℚ) (r.den:ℚ)=0:=by
      rw [←Rat.num_div_den r] at z
      unfold psiThree at z ⊢
      field_simp at z
      linear_combination z
    unfold psiThree at qr ⊢
    exact_mod_cast qr
  have reduce:psiThree (r.num:ZMod 11) (r.den:ZMod 11)=0:=by
    simpa [psiThree] using congrArg (Int.castRingHom (ZMod 11)) eqn
  obtain ⟨i,j⟩:=zero_mod_eleven _ _ reduce
  have pi:(11:ℤ)∣r.num:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp i
  have pj:11∣r.den:=(ZMod.natCast_eq_zero_iff _ _).mp j
  have both:11∣r.num.natAbs.gcd r.den:=Nat.dvd_gcd (by simpa using Int.natAbs_dvd_natAbs.mpr pi) pj
  rw [r.reduced.gcd_eq_one] at both
  norm_num at both

private theorem pos_nonsquares : ¬IsSquare (1120:ℚ) ∧ ¬IsSquare (105:ℚ) := by
  constructor
  · rintro ⟨k,e⟩
    have z:=(Rat.exists_mul_self 1120).mp ⟨k,e.symm⟩
    norm_num [Rat.sqrt_ofNat,show Nat.sqrt 1120=33 by symm;exact Nat.eq_sqrt.mpr (by decide)] at z
  · rintro ⟨k,e⟩
    have z:=(Rat.exists_mul_self 105).mp ⟨k,e.symm⟩
    norm_num [Rat.sqrt_ofNat,show Nat.sqrt 105=10 by symm;exact Nat.eq_sqrt.mpr (by decide)] at z

/-- For a rational half of a root, the square of its distance from that root
equals the product of the other two root differences. -/
theorem no_halving_products (m z:ℚ) (mn:m≠0) :
    z^2≠ -96*m^2 ∧ z^2≠1120*m^2 ∧ z^2≠105*m^2 := by
  refine ⟨by nlinarith only [sq_nonneg z,sq_pos_of_ne_zero mn],?_,?_⟩
  · intro h
    apply pos_nonsquares.1
    refine ⟨z/m,?_⟩
    field_simp;linear_combination -h
  · intro h
    apply pos_nonsquares.2
    refine ⟨z/m,?_⟩
    field_simp;linear_combination -h

/-- The duplication abscissa on the split Weierstrass model. -/
def doubledX (m x y:ℚ) := ((3*x^2-58*m*x-96*m^2)/(2*y))^2 +29*m-2*x

theorem doubled_not_root {m x y:ℚ} (mn:m≠0) (yn:y≠0)
    (curve:y^2=x*(x-32*m)*(x+3*m)) :
    doubledX m x y≠0 ∧ doubledX m x y≠32*m ∧ doubledX m x y≠ -3*m := by
  let roots (r:ℚ) (h:doubledX m x y=r) : (x^2+96*m^2)^2=4*r*y^2 := by
    unfold doubledX at h
    have e:= (div_pow ((3*x^2-58*m*x-96*m^2):ℚ) (2*y) 2)
    rw [e] at h
    field_simp at h
    linear_combination h-(4*(29*m-2*x))*curve
  constructor
  · intro e
    have Q:=roots 0 e
    have pos:0<(x^2+96*m^2)^2:=sq_pos_of_pos (by nlinarith only [sq_nonneg x,sq_pos_of_ne_zero mn])
    nlinarith only [Q,pos]
  constructor
  · intro e
    have z:=roots (32*m) e
    have sq:((x-32*m)^2-1120*m^2)^2=0:=by
      linear_combination z+128*m*curve
    have h: (x-32*m)^2=1120*m^2 := sub_eq_zero.mp ((sq_eq_zero_iff).mp sq)
    exact (no_halving_products m (x-32*m) mn).2.1 h
  · intro e
    have z:=roots (-3*m) e
    have sq:((x+3*m)^2-105*m^2)^2=0:=by
      linear_combination z-12*m*curve
    have h:(x+3*m)^2=105*m^2:=sub_eq_zero.mp ((sq_eq_zero_iff).mp sq)
    exact (no_halving_products m (x+3*m) mn).2.2 h

theorem doubled_ne_self {m x y:ℚ} (mn:m≠0) (yn:y≠0)
    (curve:y^2=x*(x-32*m)*(x+3*m)) : doubledX m x y≠x := by
  intro h
  apply no_three_root (x/m)
  unfold doubledX at h
  rw [div_pow] at h
  field_simp at h
  unfold psiThree
  field_simp
  linear_combination -h+(4*(29*m-3*x))*curve

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.no_three_root
#print axioms Sun28.ScalarQuotients.no_halving_products
#print axioms Sun28.ScalarQuotients.doubled_not_root
#print axioms Sun28.ScalarQuotients.doubled_ne_self
