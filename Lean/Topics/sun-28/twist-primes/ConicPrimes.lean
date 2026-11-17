import NewTwistPrimes

namespace Sun28.TwistPrimes
open PairedClasses PreparedPoles ZInQ.RouteK

/-- For k=(a²+β)/(2a) the first quartic factor is a square, and this
polynomial represents the second factor up to the square (2a)². -/
def conicValue (β a : ℕ) : ℕ := 9*a^4+14*β*a^2+9*β^2

set_option maxHeartbeats 2000000 in
private theorem mod24_sqfreepart : ∀ t h : ZMod 24, t*h^2=1 → t=1 := by
  decide

/-- The new conic family satisfies all simultaneous-twist local conditions
at the two sets of support primes, and its witnesses use the same n=β. -/
theorem conic_family {β a : ℕ} (hb : 0<β) (sb : Squarefree β)
    (b6 : β.Coprime 6) (bm : β%24=17) (ha : 0<a) (even : 2∣a)
    (a3 : ¬3∣a) (ba : β.Coprime a) :
    ∃ θ h : ℕ, conicValue β a=θ*h^2 ∧ AdmissiblePair β θ ∧ Family β θ ∧
      TwistPoint β β ∧ TwistPoint β (β*θ) := by
  have b17 : 17≤β := by omega
  have nz : 0<conicValue β a := by dsimp [conicValue]; positivity
  obtain ⟨h,hn,eq⟩ := sqfNat_mul_sq nz.ne'
  let θ := sqfNat (conicValue β a)
  have E : conicValue β a=θ*h^2 := eq
  have nt : θ≠0 := by intro z; rw [z,zero_mul] at E; omega
  have st : Squarefree θ := sqfNat_squarefree _
  have eql (p : ℕ) : (9*(a:ZMod p)^4+14*β*a^2+9*β^2)=(θ:ZMod p)*h^2 := by
    simpa [conicValue] using congrArg (fun n : ℕ=>(n:ZMod p)) E
  have tm : θ%24=1 := by
    have u := eql 24
    have rr : (β:ZMod 24)=17 := (ZMod.natCast_eq_natCast_iff' _ 17 24).mpr bm
    rw [rr] at u
    obtain ⟨j,ej⟩ := even
    have j3 : ¬3∣j := fun d=>a3 (ej ▸ dvd_mul_of_dvd_right d 2)
    have cert : ∀ x : ZMod 24, x*8≠0 → (9*(2*x)^4+14*17*(2*x)^2+9*17^2 : ZMod 24)=1 := by decide
    have non : (j:ZMod 24)*8≠0 := by
      intro z
      have d : 24∣j*8 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using z)
      apply j3
      obtain ⟨v,hv⟩ := d
      exact ⟨v,by omega⟩
    rw [ej,Nat.cast_mul,Nat.cast_ofNat,cert j non] at u
    exact (ZMod.natCast_eq_natCast_iff' _ 1 24).mp (mod24_sqfreepart _ _ u.symm)
  have c6 : θ.Coprime 6 := by
    have d : Nat.gcd θ 6=Nat.gcd (θ%6) 6 := (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _)
    change Nat.gcd θ 6=1
    rw [d,show θ%6=1 by omega]
    decide
  have atB (p : ℕ) (pp : p.Prime) (db : p∣β) :
      let : Fact p.Prime := ⟨pp⟩
      (θ:ZMod p)≠0 ∧ IsSquare (θ:ZMod p) := by
    let : Fact p.Prime := ⟨pp⟩
    have aunit : (a:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
      (fun d =>pp.not_dvd_one (ba ▸ Nat.dvd_gcd db d))
    have three : (3:ZMod p)≠0 := by
      exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).not.mpr
        (fun d=>pp.not_dvd_one (b6 ▸ Nat.dvd_gcd db (d.trans (by decide))))
    have non : (3*(a:ZMod p)^2)^2≠0 := pow_ne_zero _ (mul_ne_zero three (pow_ne_zero _ aunit))
    have e := eql p
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr db] at e
    have z : (3*(a:ZMod p)^2)^2=θ*h^2 := by linear_combination e
    have hu : (h:ZMod p)≠0 := by intro zero; apply non; simpa only [zero,pow_two,zero_mul,mul_zero] using z
    have tu : (θ:ZMod p)≠0 := by intro zero; apply non; simpa [zero] using z
    refine ⟨tu,3*(a:ZMod p)^2/h,?_⟩
    field_simp
    linear_combination -z
  have disjoint : β.Coprime θ := by
    by_contra nd
    obtain ⟨p,pp,db,dt⟩ := Nat.Prime.not_coprime_iff_dvd.mp nd
    exact (atB p pp db).1 ((ZMod.natCast_eq_zero_iff _ _).mpr dt)
  have ad : AdmissiblePair β θ := by
    refine ⟨hb,Nat.pos_of_ne_zero nt,sb,st,disjoint,b6,c6,bm,tm,?_,?_⟩
    · intro p pp dt
      let : Fact p.Prime := ⟨pp⟩
      have no2 : p≠2 := by rintro rfl; omega
      have bn : (β:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
        (fun db=>pp.not_dvd_one (disjoint ▸ Nat.dvd_gcd db dt))
      have three : (3:ZMod p)≠0 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).not.mpr
          (fun d=>pp.not_dvd_one (c6 ▸ Nat.dvd_gcd dt (d.trans (by decide))))
      have two : (2:ZMod p)≠0 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr
          (fun d=>pp.not_dvd_one (c6 ▸ Nat.dvd_gcd dt (d.trans (by decide))))
      have e := eql p
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr dt,zero_mul] at e
      have id : (3*((a:ZMod p)^2+β))^2=β*(2*a)^2 := by linear_combination e
      have au : (a:ZMod p)≠0 := by
        intro zero
        have bad : (3*(β:ZMod p))^2=0 := by simpa [zero] using id
        exact pow_ne_zero 2 (mul_ne_zero three bn) bad
      apply local_square_of_legendre no2 ((legendreSym.eq_one_iff' p bn).mpr ?_)
      refine ⟨3*((a:ZMod p)^2+β)/(2*a),?_⟩
      field_simp
      linear_combination -id
    · intro p pp db
      let : Fact p.Prime := ⟨pp⟩
      have no2 : p≠2 := by rintro rfl; omega
      exact local_square_of_legendre no2 ((legendreSym.eq_one_iff' p (atB p pp db).1).mpr (atB p pp db).2)
  have neq : (a:ℚ)^2≠β := by
    intro e
    have z : a^2=β := by exact_mod_cast e
    have d : 4∣β := z ▸ (show 4∣a^2 by simpa using pow_dvd_pow_of_dvd even 2)
    omega
  have pos : (a:ℚ)≠0 := by exact_mod_cast ha.ne'
  have nh : (h:ℚ)≠0 := by exact_mod_cast hn
  have zq : (9*(a:ℚ)^4+14*(β:ℚ)*a^2+9*(β:ℚ)^2)=(θ:ℚ)*h^2 := by
    simpa [conicValue] using congrArg (fun n : ℕ=>(n:ℚ)) E
  have fam : Family β θ := by
    refine ⟨((a:ℚ)^2+β)/(2*a),((a:ℚ)^2-β)*h/(4*a^2),by
      exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr neq) nh) (mul_ne_zero (by norm_num) (pow_ne_zero _ pos)),?_⟩
    field_simp
    linear_combination 16 * ((a:ℚ)^2-β)^2 * zq
  exact ⟨θ,h,E,ad,fam,fixed_points_of_family hb (Nat.pos_of_ne_zero nt) fam⟩

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.conic_family
