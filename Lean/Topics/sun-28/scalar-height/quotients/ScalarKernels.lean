import LocalScalar

namespace Sun28.ScalarQuotients
open ZInQ.RouteK
noncomputable section

/-- Two distinct binary forms can vanish at a primitive pair modulo a prime only
when their coefficient determinant vanishes. -/
theorem prime_divides_determinant {a b A B C D:ℤ} {p:ℕ} (pp:p.Prime)
    (ab:a.natAbs.Coprime b.natAbs) (h:(p:ℤ)∣A*a^2+B*b^2) (j:(p:ℤ)∣C*a^2+D*b^2) :
    (p:ℤ)∣A*D-B*C := by
  have ip:=Nat.prime_iff_prime_int.mp pp
  by_contra hn
  have aa:(p:ℤ)∣(A*D-B*C)*a^2:=by
    convert dvd_sub (dvd_mul_of_dvd_left h D) (dvd_mul_of_dvd_left j B) using 1;ring
  have bb:(p:ℤ)∣(A*D-B*C)*b^2:=by
    convert dvd_sub (dvd_mul_of_dvd_left j A) (dvd_mul_of_dvd_left h C) using 1;ring
  have pa:=ip.dvd_of_dvd_pow ((ip.dvd_mul.mp aa).resolve_left hn)
  have pb:=ip.dvd_of_dvd_pow ((ip.dvd_mul.mp bb).resolve_left hn)
  exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt
    (by simpa using Int.natAbs_dvd_natAbs.mpr pa)
    (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) ab

/-- In U V = d Y² the squarefree part k of a positive factor U divides d V. -/
theorem squarefree_factor {U V d Y:ℤ} (pos:0<U) (E:U*V=d*Y^2) :
    ∃ k:ℕ, ∃ v:ℤ, Squarefree k ∧ U=(k:ℤ)*v^2 ∧ (k:ℤ)∣d*V := by
  let k:=sqfNat U.natAbs
  have sf:Squarefree k:=sqfNat_squarefree _
  obtain ⟨v,vn,ev⟩:=sqfNat_mul_sq (Int.natAbs_ne_zero.mpr pos.ne')
  have e:U=(k:ℤ)*(v:ℤ)^2:=by
    have t:=congrArg (fun n:ℕ=>(n:ℤ)) ev
    simpa [k,Int.natAbs_of_nonneg pos.le] using t
  refine ⟨k,v,sf,e,?_⟩
  have H: IsSquare (((k:ℤ)*(d*V):ℤ):ℚ):=by
    refine ⟨(d:ℚ)*Y/v,?_⟩
    have eq:((k:ℚ)*(v:ℚ)^2)*V=(d:ℚ)*(Y:ℚ)^2:=by exact_mod_cast e ▸ E
    push_cast
    field_simp
    linear_combination (d:ℚ)*eq
  obtain ⟨w,hw⟩:=Rat.isSquare_intCast_iff.mp H
  have zw:(k:ℤ)∣w^2:=by rw [sq,←hw];exact dvd_mul_right .. 
  obtain ⟨t,ht⟩:=((Int.squarefree_natCast.mpr sf).dvd_pow_iff_dvd (by decide : 2≠0)).mp zw
  refine ⟨t^2,?_⟩
  apply mul_left_cancel₀ (show (k:ℤ)≠0 by exact_mod_cast sf.ne_zero)
  rw [hw,ht];ring

private theorem support_product {k N:ℕ} (sf:Squarefree k) (nz:N≠0)
    (h:∀ p:ℕ,p.Prime → p∣k → p∣N) : k∣N := by
  rw [←Nat.prod_primeFactors_of_squarefree sf,Nat.prod_primeFactors_dvd_iff nz]
  intro p hp
  have pp:=Nat.prime_of_mem_primeFactors hp
  exact Nat.mem_primeFactors.mpr ⟨pp,h _ pp (Nat.dvd_of_mem_primeFactors hp),nz⟩

private theorem determinant_support {p:ℕ} (pp:p.Prime) (z:ℤ) (N:ℕ) (e:∃n:ℕ, z.natAbs∣N^n)
    (h:(p:ℤ)∣z) : p∣N := by
  obtain ⟨n,ne⟩:=e
  apply pp.dvd_of_dvd_pow (n:=n)
  exact (show p∣z.natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans ne

/-- Only the primes of 14d and 30d can divide the first two signed kernels. -/
theorem two_kernels {a b d Y:ℤ} (ab:a.natAbs.Coprime b.natAbs) (bn:b≠0) (dn:d≠0)
    (E:homogenized a b=d*Y^2) :
    ∃ k l:ℕ, ∃ u v:ℤ, k∣14*d.natAbs ∧ l∣30*d.natAbs ∧
      2*a^2+3*b^2=(k:ℤ)*u^2 ∧ a^2+b^2=(l:ℤ)*v^2 := by
  let A:=2*a^2+3*b^2
  let B:=a^2+b^2
  let C:=a^2-1199*b^2
  let D:=64*a^2+439*b^2
  change A*B*C*D=d*Y^2 at E
  have bs:=sq_pos_of_ne_zero bn
  obtain ⟨k,u,hk,eqk,hkd⟩:=squarefree_factor
    (show 0<A by dsimp [A];nlinarith only [bs,sq_nonneg a])
    (show A*(B*C*D)=d*Y^2 by linear_combination E)
  obtain ⟨l,v,hl,eql,hld⟩:=squarefree_factor
    (show 0<B by dsimp [B];nlinarith only [bs,sq_nonneg a])
    (show B*(A*C*D)=d*Y^2 by linear_combination E)
  refine ⟨k,l,u,v,?_,?_,eqk,eql⟩
  · apply support_product hk (mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr dn))
    intro p pp pk
    have ip:=Nat.prime_iff_prime_int.mp pp
    have kp:(p:ℤ)∣k:=by exact_mod_cast pk
    have left:(p:ℤ)∣A:=eqk ▸ dvd_mul_of_dvd_left kp _
    rcases ip.dvd_mul.mp (kp.trans hkd) with pd|pr
    · exact dvd_mul_of_dvd_right (by simpa using Int.natAbs_dvd_natAbs.mpr pd) _
    apply dvd_mul_of_dvd_left
    rcases ip.dvd_mul.mp pr with pr|pr
    · rcases ip.dvd_mul.mp pr with pr|pr
      · exact determinant_support pp _ 14 ⟨1,by decide⟩ (prime_divides_determinant pp ab left (show (p:ℤ)∣1*a^2+1*b^2 by simpa [B] using pr))
      · exact determinant_support pp _ 14 ⟨4,by decide⟩ (prime_divides_determinant pp ab left (show (p:ℤ)∣1*a^2+(-1199)*b^2 by simpa [C,sub_eq_add_neg] using pr))
    · exact determinant_support pp _ 14 ⟨3,by decide⟩ (prime_divides_determinant pp ab left pr)
  · apply support_product hl (mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr dn))
    intro p pp pl
    have ip:=Nat.prime_iff_prime_int.mp pp
    have lp:(p:ℤ)∣l:=by exact_mod_cast pl
    have left:(p:ℤ)∣1*a^2+1*b^2:=by simpa only [one_mul,←eql] using (eql ▸ dvd_mul_of_dvd_left lp (v^2) : (p:ℤ)∣B)
    rcases ip.dvd_mul.mp (lp.trans hld) with pd|pr
    · exact dvd_mul_of_dvd_right (by simpa using Int.natAbs_dvd_natAbs.mpr pd) _
    apply dvd_mul_of_dvd_left
    rcases ip.dvd_mul.mp pr with pr|pr
    · rcases ip.dvd_mul.mp pr with pr|pr
      · exact determinant_support pp _ 30 ⟨1,by decide⟩ (prime_divides_determinant pp ab left pr)
      · exact determinant_support pp _ 30 ⟨4,by decide⟩ (prime_divides_determinant pp ab left (show (p:ℤ)∣1*a^2+(-1199)*b^2 by simpa [C,sub_eq_add_neg] using pr))
    · exact determinant_support pp _ 30 ⟨3,by decide⟩ (prime_divides_determinant pp ab left pr)
end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.prime_divides_determinant
#print axioms Sun28.ScalarQuotients.squarefree_factor
#print axioms Sun28.ScalarQuotients.two_kernels
