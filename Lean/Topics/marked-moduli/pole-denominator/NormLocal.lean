import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-! Local cancellation in the reduced pole norm for the six marked parameters. -/
namespace ZInQBlueprint.PoleNorm

def norm (p q : ℤ) : ℤ := p^2+3*q^2
def sineNumerator (p q : ℤ) : ℤ := 8*p*q*(p^2-q^2)*(p^2-9*q^2)
def dyadicFactor (p q : ℤ) : ℤ := if p % 2 = 1 ∧ q % 2 = 1 then 4 else 1
def triadicFactor (p : ℤ) : ℤ := if p % 3 = 0 then 3 else 1
def factor (p q : ℤ) : ℤ := dyadicFactor p q * triadicFactor p

private theorem common_zero {p q : ℤ} (hc : IsCoprime p q) (l : ℕ) [Fact l.Prime] :
    (p : ZMod l) = 0 → (q : ZMod l) = 0 → False := by
  intro h₁ h₂
  obtain ⟨a,b,h⟩ := hc
  have h' := congrArg (fun z : ℤ => (z : ZMod l)) h
  push_cast at h'
  simp [h₁,h₂] at h'

/-- A common prime of the norm and the numerator must be 2 or 3. -/
theorem prime_exception {p q : ℤ} (hc : IsCoprime p q) {l : ℕ} (hl : l.Prime)
    (hN : (l:ℤ) ∣ norm p q) (hU : (l:ℤ) ∣ sineNumerator p q) : l=2 ∨ l=3 := by
  by_contra! he
  let _ : Fact l.Prime := ⟨hl⟩
  have nz2 : (2:ZMod l) ≠ 0 := by
    intro h
    exact he.1 ((Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 l).mp h) |>.resolve_left hl.ne_one)
  have nz3 : (3:ZMod l) ≠ 0 := by
    intro h
    exact he.2 ((Nat.dvd_prime Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff 3 l).mp h) |>.resolve_left hl.ne_one)
  have hn := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hN
  have hu := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hU
  unfold norm at hn
  unfold sineNumerator at hu
  push_cast at hn hu
  have hq : (q:ZMod l) ≠ 0 := by
    intro h
    apply common_zero hc l _ h
    simpa [h] using hn
  have hp : (p:ZMod l) ≠ 0 := by
    intro h
    simp [h,nz3,hq] at hn
  have sq : (p:ZMod l)^2 = -3*(q:ZMod l)^2 := by linear_combination hn
  have d₄ : (p:ZMod l)^2-(q:ZMod l)^2 = -(2^2)*(q:ZMod l)^2 := by rw [sq]; ring
  have d₁₂ : (p:ZMod l)^2-9*(q:ZMod l)^2 = -(3*2^2)*(q:ZMod l)^2 := by rw [sq]; ring
  rw [d₄,d₁₂,show (8:ZMod l)=2^3 by ring] at hu
  simp [nz2,nz3,hp,hq] at hu

private theorem norm_mod_eight (p q : ℤ) :
    norm p q % 8 = (p%8*(p%8)+3*((q%8)*(q%8)))%8 := by
  simp [norm,pow_two,Int.add_emod,Int.mul_emod]

private theorem norm_mod_two (p q : ℤ) :
    norm p q % 2 = (p%2*(p%2)+3*((q%2)*(q%2)))%2 := by
  simp [norm,pow_two,Int.add_emod,Int.mul_emod]

private theorem norm_mod_nine (p q : ℤ) :
    norm p q % 9 = (p%9*(p%9)+3*((q%9)*(q%9)))%9 := by
  simp [norm,pow_two,Int.add_emod,Int.mul_emod]

private theorem num_mod_eight (p q : ℤ) :
    (p^2-q^2)%8 = ((p%8)*(p%8)-(q%8)*(q%8))%8 := by
  simp [pow_two,Int.sub_emod,Int.mul_emod]

/-- The exact dyadic part of the norm. The quotient is an odd integer. -/
theorem dyadic_norm {p q : ℤ} (hc : IsCoprime p q) :
    ∃ k : ℤ, norm p q = dyadicFactor p q * k ∧ k % 2 = 1 := by
  have prim : ¬(p % 2 = 0 ∧ q % 2 = 0) := by
    rintro ⟨h,j⟩
    apply common_zero hc 2
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mpr (Int.dvd_of_emod_eq_zero h)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mpr (Int.dvd_of_emod_eq_zero j)
  unfold dyadicFactor
  split
  · rename_i h
    have a : norm p q % 8=4 := by
      rw [norm_mod_eight]
      have i : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by omega
      have j : q%8=1 ∨ q%8=3 ∨ q%8=5 ∨ q%8=7 := by omega
      rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> rw [i,j] <;> decide
    exact ⟨norm p q / 4,by omega,by omega⟩
  · rename_i h
    have a : norm p q % 2=1 := by
      rw [norm_mod_two]
      have i : p%2=0 ∨ p%2=1 := by omega
      have j : q%2=0 ∨ q%2=1 := by omega
      rcases i with i|i <;> rcases j with j|j <;> first | (exfalso; omega) | (rw [i,j]; decide)
    exact ⟨norm p q,by ring,a⟩

/-- At three the quotient after removing a single factor of three is always a unit. -/
theorem triadic_norm {p q : ℤ} (hc : IsCoprime p q) :
    ∃ k : ℤ, norm p q = triadicFactor p * k ∧ k % 3 ≠ 0 := by
  have prim : ¬(p % 3 = 0 ∧ q % 3 = 0) := by
    rintro ⟨h,j⟩
    apply common_zero hc 3
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd p 3).mpr (Int.dvd_of_emod_eq_zero h)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd q 3).mpr (Int.dvd_of_emod_eq_zero j)
  unfold triadicFactor
  split
  · rename_i h
    have a : norm p q % 9 = 3 := by
      rw [norm_mod_nine]
      have i : p%9=0 ∨ p%9=3 ∨ p%9=6 := by omega
      have j : q%9=1 ∨ q%9=2 ∨ q%9=4 ∨ q%9=5 ∨ q%9=7 ∨ q%9=8 := by omega
      rcases i with i|i|i <;> rcases j with j|j|j|j|j|j <;> rw [i,j] <;> decide
    exact ⟨norm p q/3,by omega,by omega⟩
  · rename_i h
    have a : norm p q %3 ≠ 0 := by
      have hm : norm p q % 3=(p%3*(p%3))%3 := by
        simp [norm,pow_two,Int.add_emod,Int.mul_emod]
      rw [hm]
      have i : p%3=1 ∨ p%3=2 := by omega
      rcases i with i|i <;> rw [i] <;> decide
    exact ⟨norm p q,by ring,a⟩

/-- The numerator contains the cubes of the required dyadic and triadic factors. -/
theorem factor_cube_dvd (p q : ℤ) : (factor p q)^3 ∣ sineNumerator p q := by
  have hd : dyadicFactor p q ^ 3 ∣ sineNumerator p q := by
    unfold dyadicFactor
    split
    · rename_i h
      have he : (p^2-q^2)%8=0 := by
        rw [num_mod_eight]
        have i : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by omega
        have j : q%8=1 ∨ q%8=3 ∨ q%8=5 ∨ q%8=7 := by omega
        rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> rw [i,j] <;> decide
      obtain ⟨v,hv⟩ := Int.dvd_of_emod_eq_zero he
      refine ⟨p*q*v*(p^2-9*q^2), ?_⟩
      unfold sineNumerator
      rw [hv]
      ring
    · simp
  have ht : triadicFactor p ^ 3 ∣ sineNumerator p q := by
    unfold triadicFactor
    split
    · rename_i h
      obtain ⟨v,rfl⟩ := Int.dvd_of_emod_eq_zero h
      exact ⟨8*v*q*(9*v^2-q^2)*(v^2-q^2), by unfold sineNumerator; ring⟩
    · simp
  have cop : IsCoprime (dyadicFactor p q ^3) (triadicFactor p ^3) := by
    unfold dyadicFactor triadicFactor
    split <;> split <;> decide
  rw [factor,mul_pow]
  exact cop.mul_dvd hd ht

end ZInQBlueprint.PoleNorm
#print axioms ZInQBlueprint.PoleNorm.prime_exception
#print axioms ZInQBlueprint.PoleNorm.dyadic_norm
#print axioms ZInQBlueprint.PoleNorm.triadic_norm
#print axioms ZInQBlueprint.PoleNorm.factor_cube_dvd
