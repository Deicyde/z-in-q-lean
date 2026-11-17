import MultiplierClass
import UnitLifting

namespace Sun28.PreparedPoles
open ZInQ.RouteK ZInQ Sun28.FixedPreparation

/-- Decode the prepared local depths at every prime of Sun's actual multiplier list. -/
theorem numerator_depth {B : ℚ} (h : Prepared B) {p : ℕ} (pp : p.Prime) (mem : p∈primes) :
    ¬p∣B.den ∧ (p:ℤ)^4∣B.num := by
  let _ := Fact.mk pp
  have val := h.2.2.2 p mem
  have bn := Rat.num_pos.mpr h.2.1
  unfold padicValRat at val
  have den : ¬p∣B.den := by
    intro e
    have num : ¬(p:ℤ)∣B.num := by
      intro n
      exact pp.ne_one (Nat.dvd_one.mp (B.reduced ▸ Nat.dvd_gcd (Int.natCast_dvd.mp n) e))
    rw [padicValInt.eq_zero_of_not_dvd num] at val
    omega
  rw [padicValNat.eq_zero_of_not_dvd den] at val
  exact ⟨den,(padicValInt_dvd_iff 4 B.num).mpr (Or.inr (by omega))⟩

private def Supported (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p:ℤ)∣m → p∈primes ∧ ¬(p:ℤ)^2∣m

/-- If m has squarefree support in the nine fixed primes, reducing B=a/k²
gives two primitive integer factorizations and (mk)²=βs²+θc². -/
private theorem setup {B : ℚ} (h : Prepared B) {m : ℤ} (mp : 0 < m) :
    ∃ (a k s c : ℤ), 0 < a ∧ 0 < k ∧ IsCoprime a k ∧
    (∀ p∈primes, p.Prime → ¬(p:ℤ)∣k ∧ (p:ℤ)^4∣a) ∧
    Squarefree (betaOf B m) ∧ Squarefree (thetaOf B m) ∧
    m*a=betaOf B m*s^2 ∧ thetaOf B m*c^2=(m*k)^2-m*a := by
  have ad := prepared_admissible h
  obtain ⟨k,hk,hnum,_,cop,_⟩:=ad.decode
  have mr : (m:ℚ)≠B := by
    have m1 : (1:ℚ)≤ m := by exact_mod_cast (show 1≤ m by omega)
    linarith [h.2.2.1]
  obtain ⟨b,t⟩ := betaOf_thetaOf_eq_sqfInt hk mp.ne' h.2.1.ne' mr
  have nk : 0 < k := Nat.pos_of_ne_zero (fun z => B.den_ne_zero (by simpa only [z,zero_pow two_ne_zero] using hk))
  obtain ⟨bs,s,_,hs⟩ := sqfInt_spec (mul_ne_zero mp.ne' hnum.ne')
  have θn : (m*(k:ℤ))^2-m*B.num≠0 := by
    intro z
    have e : m*(m*(k:ℤ)^2-B.num)=0 := by linear_combination z
    have za := (mul_eq_zero.mp e).resolve_left mp.ne'
    apply mr
    rw [← Rat.num_div_den B,eq_div_iff (by exact_mod_cast B.den_ne_zero)]
    exact_mod_cast (show m*(B.den:ℤ)=B.num by rw [hk];push_cast;linarith)
  obtain ⟨ts,c,_,hc⟩ := sqfInt_spec θn
  rw [←b] at bs hs
  rw [←t] at ts hc
  refine ⟨B.num,k,s,c,hnum,by exact_mod_cast nk,cop,?_,bs,ts,hs,hc.symm⟩
  intro p mem pp
  obtain ⟨nd,deep⟩ := numerator_depth h pp mem
  refine ⟨fun d => nd (hk ▸ dvd_pow (Int.natCast_dvd_natCast.mp d) two_ne_zero),deep⟩

private theorem local_prepared {p : ℕ} (pp : p.Prime) {m a k θ c : ℤ}
    (mem : ¬(p:ℤ)^2∣m) (den : ¬(p:ℤ)∣k) (deep : (p:ℤ)^4∣a)
    (sf : Squarefree θ) (eqn : θ*c^2=(m*k)^2-m*a) :
    ¬(p:ℤ)∣θ ∧ ∃ x y : ℤ, ¬(p:ℤ)∣x ∧ ¬(p:ℤ)∣y ∧ θ*x^2≡y^2 [ZMOD (p:ℤ)^3] := by
  have pr := Nat.prime_iff_prime_int.mp pp
  obtain ⟨b,rfl⟩:=deep
  by_cases pm : (p:ℤ)∣m
  · obtain ⟨d,rfl⟩ := pm
    have d0 : ¬(p:ℤ)∣d := fun e => mem (by rw [sq];exact mul_dvd_mul_left _ e)
    have u : ¬(p:ℤ)∣d*k := fun e => (pr.dvd_or_dvd e).elim d0 den
    obtain ⟨t,x,nx,hx⟩ := local_unit_square (e:=1) (j:=3) (X:=(p:ℤ)*d*((p:ℤ)^4*b))
      pp (by decide) sf u ⟨d*b,by ring⟩ (by rw [eqn];ring)
    exact ⟨t,x,d*k,nx,u,hx⟩
  · have u : ¬(p:ℤ)∣m*k := fun e => (pr.dvd_or_dvd e).elim pm den
    obtain ⟨t,x,nx,hx⟩ := local_unit_square (e:=0) (j:=3) (X:=m*((p:ℤ)^4*b))
      pp (by decide) sf u ⟨m*(p:ℤ)*b,by ring⟩ (by rw [eqn];ring)
    exact ⟨t,x,m*k,nx,u,hx⟩

private theorem support_beta {p : ℕ} [fact : Fact p.Prime] {m a k β θ s c : ℤ}
    (cop : IsCoprime a k) (u : ¬(p:ℤ)∣m) (sf : Squarefree θ) (bs : m*a=β*s^2)
    (ts : θ*c^2=(m*k)^2-m*a) (div : (p:ℤ)∣β) :
    ¬(p:ℤ)∣θ ∧ legendreSym p θ=1 := by
  have pr:=Nat.prime_iff_prime_int.mp fact.out
  have pa : (p:ℤ)∣m*a := bs ▸ dvd_mul_of_dvd_left div _
  have nd : ¬(p:ℤ)∣k := fun e => pr.not_isUnit (cop.isUnit_of_dvd' ((pr.dvd_or_dvd pa).resolve_left u) e)
  have nz : ¬(p:ℤ)∣m*k := fun e => (pr.dvd_or_dvd e).elim u nd
  obtain ⟨out,x,xn,hx⟩ := local_unit_square (e:=0) (j:=1) (X:=m*a) fact.out le_rfl sf nz
    (by simpa using pa) (by simpa using ts)
  exact ⟨out,legendreSym_eq_one_of_modEq xn nz (by simpa using hx)⟩

private theorem support_theta {p : ℕ} [fact : Fact p.Prime] {m a k β θ s c : ℤ}
    (cop : IsCoprime a k) (u : ¬(p:ℤ)∣m) (bs : m*a=β*s^2)
    (ts : θ*c^2=(m*k)^2-m*a) (div : (p:ℤ)∣θ) : legendreSym p β=1 := by
  have pr:=Nat.prime_iff_prime_int.mp fact.out
  have diff : (p:ℤ)∣(m*k)^2-m*a := ts ▸ dvd_mul_of_dvd_left div _
  have nd : ¬(p:ℤ)∣k := by
    intro e
    have h := dvd_sub (dvd_pow (dvd_mul_of_dvd_right e m) two_ne_zero) diff
    rw [sub_sub_cancel] at h
    exact pr.not_isUnit (cop.isUnit_of_dvd' ((pr.dvd_or_dvd h).resolve_left u) e)
  have nz : ¬(p:ℤ)∣m*k := fun e => (pr.dvd_or_dvd e).elim u nd
  have ma : ¬(p:ℤ)∣m*a := by
    intro e
    have h := dvd_add diff e
    rw [sub_add_cancel] at h
    exact nz (pr.dvd_of_dvd_pow h)
  have sn : ¬(p:ℤ)∣s := fun e => ma (bs ▸ dvd_mul_of_dvd_right (dvd_pow e two_ne_zero) _)
  apply legendreSym_eq_one_of_modEq sn nz
  rw [←bs]; exact Int.modEq_iff_dvd.mpr diff

private theorem unit_square_mod3 (x : ℤ) (nd : ¬(3:ℤ)∣x) : x^2 ≡ 1 [ZMOD 3] := by
  have e : x ≡ x%3 [ZMOD 3] := by simp [Int.ModEq]
  have c : x%3=1 ∨ x%3=2 := by omega
  rcases c with h|h <;> (apply (e.pow 2).trans; rw [h]; decide)

structure PreparedClasses (B : ℚ) (m : ℤ) (β θ : ℕ) : Prop where
  beta_positive : 0 < β
  theta_positive : 0 < θ
  beta_sf : Squarefree β
  theta_sf : Squarefree θ
  disjoint : β.Coprime θ
  beta_six : β.Coprime 6
  theta_six : θ.Coprime 6
  beta_mod : β%24=17
  theta_mod : θ%24=1
  beta_local : ∀ p : ℕ, p.Prime → p∣θ → LocalSquareAt p β
  theta_local : ∀ p : ℕ, p.Prime → p∣β → LocalSquareAt p θ
  beta_scale : ∃ a : ℚ, a≠0 ∧ (m:ℚ)*B=(β:ℚ)*a^2
  theta_scale : ∃ d : ℚ, d≠0 ∧ ((m:ℚ)*B)*((m:ℚ)*B-B^2)=(θ:ℚ)*d^2

theorem choose_classes {B : ℚ} (h : Prepared B) :
    ∃ (m : ℤ) (β θ : ℕ), (m:ℚ)∈ScalarHeight.smallMultipliers ∧ PreparedClasses B m β θ := by
  obtain ⟨m,mp,member,supported,bmod⟩ := choose_multiplier h.2.1
  obtain ⟨a,k,s,c,_,_,cop,deep,bs,ts,eb,et⟩ := setup h mp
  let b:=betaOf B m
  let t:=thetaOf B m
  have bp : 0 < b := (sqf_pos_iff (mul_pos (by exact_mod_cast mp) h.2.1).ne').2
    (mul_pos (by exact_mod_cast mp) h.2.1)
  have mr : B<(m:ℚ) := by
    have m1 : (1:ℚ)≤ m := by exact_mod_cast (show 1≤ m by omega)
    linarith [h.2.2.1]
  have ht : 0<(m:ℚ)*(m-B) := mul_pos (by exact_mod_cast mp) (sub_pos.mpr mr)
  have tp : 0 < t := (sqf_pos_iff ht.ne').2 ht
  have be : (b.natAbs:ℤ)=b := Int.natAbs_of_nonneg bp.le
  have te : (t.natAbs:ℤ)=t := Int.natAbs_of_nonneg tp.le
  have prep {p : ℕ} (pp : p.Prime) (mem : p∈primes) :
      ¬(p:ℤ)∣t ∧ ∃ x y : ℤ, ¬(p:ℤ)∣x ∧ ¬(p:ℤ)∣y ∧ t*x^2≡y^2 [ZMOD (p:ℤ)^3] := by
    have nd : ¬(p:ℤ)^2∣m := by
      intro e
      exact (supported p pp ((dvd_pow_self _ two_ne_zero).trans e)).2 e
    exact local_prepared pp nd (deep p mem pp).1 (deep p mem pp).2 ts et
  obtain ⟨_,x,y,xn,yn,at2⟩ := prep Nat.prime_two (by decide)
  have odd1 : Odd x := Int.not_even_iff_odd.mp fun e => xn (even_iff_two_dvd.mp e)
  have odd2 : Odd y := Int.not_even_iff_odd.mp fun e => yn (even_iff_two_dvd.mp e)
  have two : t≡1 [ZMOD 8] := by
    have z := (int_sq_modEq_one_of_odd odd1).mul_left t
    rw [mul_one] at z
    exact (z.symm.trans (by simpa using at2)).trans (int_sq_modEq_one_of_odd odd2)
  obtain ⟨_,x₃,y₃,xn₃,yn₃,at3⟩ := prep Nat.prime_three (by decide)
  have three : t≡1 [ZMOD 3] := by
    have z := (unit_square_mod3 x₃ xn₃).mul_left t
    rw [mul_one] at z
    exact (z.symm.trans (at3.of_dvd (dvd_pow_self _ (by decide)))).trans (unit_square_mod3 y₃ yn₃)
  have tmod : t%24=1 := by unfold Int.ModEq at two three;omega
  have bn : b.natAbs%24=17 := by change b%24=17 at bmod;omega
  have tn : t.natAbs%24=1 := by omega
  have c6 (u : ℕ) (r : u%24=17 ∨ u%24=1) : u.Coprime 6 := by
    have cop2 : u.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm
    have cop3 : u.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)).symm
    exact cop2.mul_right cop3
  have atB {p : ℕ} [pp : Fact p.Prime] (div : (p:ℤ)∣b) : ¬(p:ℤ)∣t ∧ legendreSym p t=1 := by
    by_cases mem : p∈primes
    · obtain ⟨nd,X,Y,nx,ny,e⟩:=prep pp.out mem
      exact ⟨nd,legendreSym_eq_one_of_modEq nx ny (e.of_dvd (dvd_pow_self _ (by decide)))⟩
    · exact support_beta cop (fun d => mem (supported p pp.out d).1) ts eb et div
  have atT {p : ℕ} [pp : Fact p.Prime] (div : (p:ℤ)∣t) : legendreSym p b=1 := by
    apply support_theta cop _ eb et div
    exact fun d => (prep pp.out (supported p pp.out d).1).1 div
  have dq {p u : ℕ} {z : ℤ} (eqn : (u:ℤ)=z) (d : p∣u) : (p:ℤ)∣z := eqn ▸ Int.natCast_dvd_natCast.mpr d
  refine ⟨m,b.natAbs,t.natAbs,member,?_⟩
  constructor
  · omega
  · omega
  · exact Int.squarefree_natAbs.mpr bs
  · exact Int.squarefree_natAbs.mpr ts
  · apply Nat.coprime_of_dvd
    intro p pp ub ut
    let _ := Fact.mk pp
    exact (atB (dq be ub)).1 (dq te ut)
  · exact c6 _ (Or.inl bn)
  · exact c6 _ (Or.inr tn)
  · exact bn
  · exact tn
  · intro p pp div
    let _ := Fact.mk pp
    apply local_square_of_legendre (by rintro rfl; omega)
    rw [be]; exact atT (dq te div)
  · intro p pp div
    let _ := Fact.mk pp
    apply local_square_of_legendre (by rintro rfl; omega)
    rw [te]; exact (atB (dq be div)).2
  · obtain ⟨_,a,an,eqn⟩:=sqf_spec (mul_pos (by exact_mod_cast mp : 0<(m:ℚ)) h.2.1).ne'
    have cast : (b.natAbs:ℚ)=(b:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun v : ℤ => (v:ℚ)) be
    exact ⟨a,an,by rw [cast];exact eqn⟩
  · obtain ⟨_,d,dn,eqn⟩:=sqf_spec ht.ne'
    refine ⟨B*d,mul_ne_zero h.2.1.ne' dn,?_⟩
    have cast : (t.natAbs:ℚ)=(t:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun v : ℤ => (v:ℚ)) te
    rw [cast]
    change (m:ℚ)*B*(m*B-B^2)=(sqf ((m:ℚ)*(m-B)):ℚ)*(B*d)^2
    linear_combination B^2*eqn

end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.numerator_depth
#print axioms Sun28.PreparedPoles.choose_classes
