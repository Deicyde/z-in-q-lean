import PhysicalFactors
import Mathlib.Data.Nat.Squarefree

namespace Sun28.ConicSelection
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unnecessarySimpa false

private theorem sqfree_extract {d q : ℤ} (hd : Squarefree d) (hs : IsSquare ((d*q:ℤ):ℚ)) :
    ∃v:ℤ, q=d*v^2 := by
  obtain ⟨W,hW⟩:=Rat.isSquare_intCast_iff.mp hs
  have dv : d∣W^2 := by rw [sq,←hW]; exact dvd_mul_right .. 
  obtain ⟨v,hv⟩:=(hd.dvd_pow_iff_dvd (by decide : 2≠0)).mp dv
  refine ⟨v,mul_left_cancel₀ hd.ne_zero ?_⟩
  rw [hW,hv]; ring

private theorem common {s:ℚ} (f:Factors s) {p:ℕ} (hp:p.Prime)
    (hP:(p:ℤ)∣f.P) (hQ:(p:ℤ)∣f.Q) : p∣7194 := by
  by_contra no
  have ip:=Nat.prime_iff_prime_int.mp hp
  have nd : ¬ (p:ℤ)∣7194 := by exact_mod_cast no
  have bpow : (p:ℤ)∣7194*f.b^4 := f.prod ▸ dvd_mul_of_dvd_left hP _
  have pb := ip.dvd_of_dvd_pow ((ip.dvd_mul.mp bpow).resolve_left nd)
  have ma : (p:ℤ)∣686*f.a^2 := by
    convert dvd_add (dvd_sub hQ hP) (dvd_mul_of_dvd_right (dvd_pow pb (by decide:2≠0)) 349) using 1
    rw [f.diff]; ring
  rcases ip.dvd_mul.mp ma with small|aa
  · have natSmall : p∣686 := by exact_mod_cast small
    have classify : ∀ n∈(686:ℕ).divisors, n.Prime → n=2 ∨ n=7 := by decide
    rcases classify p (Nat.mem_divisors.mpr ⟨natSmall,by decide⟩) hp with rfl|rfl
    · exact no (by decide)
    · exact f.odd7 pb
  · exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr (ip.dvd_of_dvd_pow aa))
      (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) f.cop

theorem four_factors {s:ℚ} (f:Factors s) :
    ∃d∈(7194:ℕ).divisors, ∃u v:ℤ, f.P=(d:ℤ)*u^2 ∧
      f.Q=(((7194:ℕ)/d:ℕ):ℤ)*v^2 ∧ u*v=f.b^2 := by
  obtain ⟨u,k,uk,hk⟩:=exists_sq_mul_squarefree f.P
  have pu : f.P=k*u^2 := by rw [←uk]; ring
  have un : u≠0 := by intro h; rw [h] at pu; have := f.Ppos; nlinarith
  have kp : 0<k := by by_contra! nk; have := mul_nonpos_of_nonpos_of_nonneg nk (sq_nonneg u); linarith only [this,pu,f.Ppos]
  let d:=k.natAbs
  have kd : (d:ℤ)=k := by dsimp [d]; omega
  have hs : IsSquare ((k*(7194*f.Q):ℤ):ℚ) := by
    refine ⟨(7194:ℚ)*(f.b:ℚ)^2/u,?_⟩
    have eqQ : (k:ℚ)*(u:ℚ)^2*(f.Q:ℚ)=7194*(f.b:ℚ)^4 := by exact_mod_cast pu ▸ f.prod
    push_cast; field_simp [show (u:ℚ)≠0 by exact_mod_cast un]
    linear_combination eqQ
  obtain ⟨v0,h0⟩:=sqfree_extract hk hs
  have kd0 : k∣7194*f.Q := ⟨v0^2,h0⟩
  have dvdD : d∣7194 := by
    change k.natAbs ∣ 7194
    rw [←Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hk),Nat.prod_primeFactors_dvd_iff (by decide:7194≠0)]
    intro p hp
    have prime:=Nat.prime_of_mem_primeFactors hp
    have hpk : (p:ℤ)∣k := Int.natAbs_dvd_natAbs.mp (by simpa [d] using Nat.dvd_of_mem_primeFactors hp)
    apply Nat.mem_primeFactors.mpr
    refine ⟨prime,?_,by decide⟩
    rcases (Nat.prime_iff_prime_int.mp prime).dvd_mul.mp (hpk.trans kd0) with hit|hq
    · exact_mod_cast hit
    · exact common f prime (pu ▸ dvd_mul_of_dvd_left hpk _) hq
  let e:=7194/d
  have deN : d*e=7194 := Nat.mul_div_cancel' dvdD
  have de : k*(e:ℤ)=7194 := by rw [←kd]; exact_mod_cast deN
  have sfD : Squarefree (7194:ℕ) := by
    have ps (p:ℕ) (pp:p.Prime) : Squarefree p := pp.squarefree
    have a:Squarefree (11*109:ℕ):=(Nat.squarefree_mul (by decide)).mpr ⟨ps _ (by decide),ps _ (by decide)⟩
    have b:Squarefree (3*(11*109):ℕ):=(Nat.squarefree_mul (by decide)).mpr ⟨ps _ (by decide),a⟩
    exact (Nat.squarefree_mul (show Nat.Coprime 2 (3*(11*109)) from by decide)).mpr ⟨ps _ (by decide),b⟩
  have es : Squarefree e := sfD.squarefree_of_dvd (deN ▸ dvd_mul_left ..)
  have hs' : IsSquare (((e:ℤ)*f.Q:ℤ):ℚ) := by
    refine ⟨(e:ℚ)*(f.b:ℚ)^2/u,?_⟩
    have eqZ : u^2*f.Q=(e:ℤ)*f.b^4 := by
      apply mul_left_cancel₀ kp.ne'
      calc k*(u^2*f.Q) = f.P*f.Q := by rw [pu]; ring
           _ = 7194*f.b^4 := f.prod
           _ = k*((e:ℤ)*f.b^4) := by rw [←de];ring
    have eqQ : (u:ℚ)^2*(f.Q:ℚ)=(e:ℚ)*(f.b:ℚ)^4:=by exact_mod_cast eqZ
    push_cast; field_simp [show (u:ℚ)≠0 by exact_mod_cast un]
    linear_combination (e:ℚ)*eqQ
  obtain ⟨v,qv⟩:=sqfree_extract (Int.squarefree_natCast.mpr es) hs'
  have uv : (u*v)^2=(f.b^2)^2 := by
    have pp:=f.prod
    rw [pu,qv] at pp
    calc (u*v)^2 = (k*(e:ℤ)*(u*v)^2)/7194 := by rw [de]; omega
         _ = f.b^4 := by
           have eq : k*(e:ℤ)*(u*v)^2=7194*f.b^4 := by convert pp using 1; ring
           rw [eq];omega
         _ = (f.b^2)^2 := by ring
  have ab : |u| * |v|=f.b^2 := by
    rw [←abs_mul]
    have eqsquare : |u*v|^2=(f.b^2)^2 := (sq_abs _).trans uv
    nlinarith only [eqsquare,abs_nonneg (u*v),sq_nonneg f.b]
  refine ⟨d,Nat.mem_divisors.mpr ⟨dvdD,by decide⟩,|u|,|v|,?_,?_,ab⟩
  · rw [sq_abs,kd]; exact pu
  · rw [sq_abs]; exact qv

end Sun28.ConicSelection
#print axioms Sun28.ConicSelection.four_factors