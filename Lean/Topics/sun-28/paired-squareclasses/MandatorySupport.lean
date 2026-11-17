import CommonSquareclass

namespace Sun28.PairedClasses
open PreparedPoles ZInQ.ValuationObstruction

/-- Every prime dividing the prescribed squarefree abscissa class is forced
into the twist parameter. This holds already on the first curve. -/
theorem beta_dvd_of_twist {β l : ℕ} (hs : Squarefree β) (hc : β.Coprime 6)
    (hl : 0<l) (pt : TwistPoint β l) : β∣l := by
  obtain ⟨t,y,ht,hy⟩ := pt
  have bn : (β:ℚ)≠0 := by exact_mod_cast hs.ne_zero
  have ln : (l:ℚ)≠0 := by exact_mod_cast hl.ne'
  have all (p : ℕ) (pp : p.Prime) (db : p∣β) : p∣l := by
    let : Fact p.Prime := ⟨pp⟩
    by_contra nd
    have no2 : p≠2 := by rintro rfl; exact Nat.prime_two.not_dvd_one (hc ▸ Nat.dvd_gcd db (by decide))
    have no3 : p≠3 := by rintro rfl; exact Nat.prime_three.not_dvd_one (hc ▸ Nat.dvd_gcd db (by decide))
    have vl : padicValRat p (l:ℚ)=0 := by rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]; rfl
    have vb : padicValRat p (β:ℚ)=1 := by
      rw [padicValRat.of_nat,←Nat.factorization_def _ pp,Nat.factorization_eq_one_of_squarefree hs pp db]; rfl
    have vx := elliptic_x_valuation_even_of_parameter_even p pp no2 no3
      ((β:ℚ)*t^2) l y (mul_ne_zero bn (pow_ne_zero _ ht)) ln (by rw [vl]; exact ⟨0,by decide⟩) hy
    obtain ⟨j,ej⟩ := vx
    rw [padicValRat.mul bn (pow_ne_zero _ ht),padicValRat.pow,vb] at ej
    omega
  refine (Nat.prod_primeFactors_of_squarefree hs) ▸ (Nat.prod_primeFactors_dvd_iff hl.ne').mpr ?_
  intro p hp
  obtain ⟨pp,db,_⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨pp,all p pp db,hl.ne'⟩

/-- The free cofactor of the twist is automatically squarefree
and prime to the requested abscissa class. -/
theorem realized_iff_cofactor {β θ : ℕ} (sb : Squarefree β) (b6 : β.Coprime 6) :
    Realized β θ ↔ ∃ m : ℕ, 0 < m ∧ Squarefree m ∧ Nat.Coprime β m ∧
      (β*m).Coprime (6*θ) ∧ TwistPoint β (β*m) ∧ TwistPoint β ((β*m)*θ) := by
  constructor
  · rintro ⟨n,hn,sn,nc,p,q⟩
    obtain ⟨m,em⟩ := beta_dvd_of_twist sb b6 hn p
    subst n
    obtain ⟨bc,_,sm⟩ := Nat.squarefree_mul_iff.mp sn
    exact ⟨m,Nat.pos_of_ne_zero (fun z => by simp [z] at hn),sm,bc,nc,p,q⟩
  · rintro ⟨m,hm,sm,bc,nc,p,q⟩
    exact ⟨β*m,Nat.mul_pos (Nat.pos_of_ne_zero sb.ne_zero) hm,(Nat.squarefree_mul bc).mpr ⟨sb,sm⟩,nc,p,q⟩

end Sun28.PairedClasses
#print axioms Sun28.PairedClasses.beta_dvd_of_twist
#print axioms Sun28.PairedClasses.realized_iff_cofactor
