import SourceTwists

namespace Sun28.PreparedPoles

private theorem lift_root {p : ℕ} [Fact p.Prime] (hp : p≠2) {A r D : ℤ}
    (Dr : (p:ℤ)∣D) (unit : ¬(p:ℤ)∣r) (root : D∣A-r^2) :
    ∃ t : ℤ, ¬(p:ℤ)∣t ∧ D*(p:ℤ)∣A-t^2 := by
  obtain ⟨u,hu⟩:=root
  have nz : (r:ZMod p)≠0 := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).not.mpr unit
  have two_d : ¬(p:ℤ)∣2 := by
    intro h; have d : p∣2 := Int.natCast_dvd_natCast.mp h
    have pp := Fact.out (p:=p.Prime)
    exact hp ((Nat.dvd_prime Nat.prime_two).1 d |>.resolve_left pp.ne_one)
  have two : (2:ZMod p)≠0 := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).not.mpr two_d
  obtain ⟨c,hc⟩ := ZMod.intCast_surjective (n:=p) ((u:ZMod p)/(2*r))
  have lift : (p:ℤ)∣u-2*r*c := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast;rw [hc];field_simp;ring
  obtain ⟨v,hv⟩ := lift
  obtain ⟨d,hd⟩ := Dr
  refine ⟨r+D*c,?_,v-d*c^2,?_⟩
  · intro e
    exact unit ((dvd_add_left (dvd_mul_of_dvd_left ⟨d,hd⟩ c)).1 e)
  · linear_combination hu + D*hv - (D*c^2)*hd

/-- A nonzero quadratic residue at an odd prime is a square at every precision. -/
theorem local_square_of_legendre {p : ℕ} [Fact p.Prime] (odd : p≠2) {a : ℕ}
    (good : legendreSym p (a:ℤ)=1) : LocalSquareAt p a := by
  have nz : (a:ZMod p)≠0 := by
    intro h
    have z := legendreSym.eq_zero_iff p (a:ℤ)
    have one := good
    rw [z.mpr (by exact_mod_cast h)] at one
    contradiction
  obtain ⟨x,hx⟩ := (legendreSym.eq_one_iff' p nz).mp good
  obtain ⟨r,hr⟩ := ZMod.intCast_surjective (n:=p) x
  have rn : ¬(p:ℤ)∣r := by
    intro e
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mpr e
    rw [hr] at z;rw [hx,z,mul_zero] at nz; exact nz rfl
  have root : (p:ℤ)∣(a:ℤ)-r^2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast;rw [hr,hx];ring
  have many (k : ℕ) : ∃ r : ℤ, ¬(p:ℤ)∣r ∧ (p:ℤ)^(k+1)∣(a:ℤ)-r^2 := by
    induction k with
    | zero => exact ⟨r,rn,by simpa using root⟩
    | succ j ih =>
      obtain ⟨s,sn,sh⟩:=ih
      simpa only [pow_succ (p:ℤ) (j+1)] using
        lift_root odd (dvd_pow_self (p:ℤ) (by omega : j+1≠0)) sn sh
  intro k
  cases k with
  | zero => exact ⟨0,by simp [Int.ModEq]⟩
  | succ j =>
    obtain ⟨t,_,h⟩:=many j
    exact ⟨t,Int.modEq_iff_dvd.mpr h⟩
end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.local_square_of_legendre
