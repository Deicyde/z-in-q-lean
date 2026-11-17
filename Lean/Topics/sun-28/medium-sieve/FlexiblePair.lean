import LargePair

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.SieveTail
noncomputable section

/-- Keep the divisor count inside the denominator sum and allow any cutoff up to the side. -/
theorem flexible_pair (A : Fin 3→ℚ) (t V cutoff : ℕ) (positive : 0<cutoff)
    (within : cutoff≤ side t) (v : V≤ side t) (i j : ↥(shifts A)) :
    (pairBound (lengthAt t) V cutoff i j:ℝ) ≤
      32*(((gap i j*(V:ℤ)^2).natAbs.divisors.card:ℝ)+1)*(envelope A+1:ℕ)^2*
        (growth (envelope A) t+1:ℕ)^2*((lengthAt t:ℝ)/cutoff) := by
  let S : ℝ := side t
  let E : ℝ := envelope A
  let G : ℝ := growth (envelope A) t
  let D : ℝ := ((gap i j*(V:ℤ)^2).natAbs.divisors.card:ℝ)+1
  let R : ℝ := cutoff
  let B := radius (lengthAt t) V i j
  let a:=Nat.sqrt (lengthAt t+(offset (dilation A) i.val).natAbs*V^2)
  let K:=gap i j*(V:ℤ)^2
  let L : ℝ := 2*B+1
  obtain ⟨ab,lmax,kmax,amax,_⟩:=radius_bounds A t V v i j
  have l : L≤E*S := by dsimp only [L,E,S,B];exact_mod_cast lmax
  have diagL : 2*(a:ℝ)+1≤L := by dsimp only [L];exact_mod_cast (by omega : 2*a+1≤2*B+1)
  have rp : 0<R := by dsimp [R]; exact_mod_cast positive
  have rs : R≤S := by dsimp [R,S]; exact_mod_cast within
  have se : 0<S := by dsimp [S];exact_mod_cast side_pos t
  have e0 : 0≤E := Nat.cast_nonneg _
  have g0 : 0≤G := Nat.cast_nonneg _
  have g1 : 1≤G := by dsimp [G];exact_mod_cast (by dsimp [growth];omega : 1≤growth (envelope A) t)
  have d1 : 1≤D := by dsimp [D];linarith only [Nat.cast_nonneg (α:=ℝ) (gap i j*(V:ℤ)^2).natAbs.divisors.card]
  have div : L/R+1≤(E+1)*(S/R) := by
    rw [←mul_div_assoc];apply (le_div_iff₀ rp).mpr
    rw [add_mul,div_mul_cancel₀ _ rp.ne',one_mul];linarith only [l,rs]
  have lb : B≤envelope A*lengthAt t := by
    have h:=Nat.mul_le_mul_left (envelope A) (show side t≤lengthAt t by
      dsimp [lengthAt];nlinarith only [side_pos t, Nat.mul_le_mul_left (side t) (side_pos t)])
    change 2*B+1≤envelope A*side t at lmax
    omega
  have harm := (harmonic_le_one_add_log B).trans (by linarith only [(small_log _ t B lb).2] : 1+Real.log (B:ℝ)≤1+G)
  have hn : 0≤(harmonic B:ℝ) := by rw [harmonic_eq_sum_Icc,Rat.cast_sum];exact Finset.sum_nonneg fun _ _=>by positivity
  have length : L*(harmonic B:ℝ)+B ≤ (E+1)*S*(G+2) := by
    have bnd : (B:ℝ)≤L := by dsimp [L]; linarith only [Nat.cast_nonneg (α:=ℝ) B]
    have a' := mul_le_mul l harm hn (mul_nonneg e0 se.le)
    nlinarith only [a',bnd,l,se.le,mul_nonneg e0 se.le,mul_nonneg se.le g0]
  have base : (0:ℝ) ≤ S/R := div_nonneg se.le rp.le
  have lgk : (Nat.log 2 (K.natAbs+2*B):ℝ)≤G := by dsimp [G,B,K];exact_mod_cast (small_log _ t _ kmax).1
  have lga : (Nat.log 2 (a^2+1):ℝ)≤G := by dsimp [G,a];exact_mod_cast (small_log _ t _ amax).1
  have size : (pairBound (lengthAt t) V cutoff i j:ℝ) ≤
      D*(8*G*((E+1)*(S/R)))*((E+1)*S*(G+2)) := by
    by_cases eq : i=j
    · rw [pairBound,ite_eq_left eq]
      push_cast
      have h1 : (2*(a:ℝ)+1)*(Nat.log 2 (a^2+1):ℝ)*( (2*(a:ℝ)+1)/R+1) ≤
          ( (E+1)*S)*G*((E+1)*(S/R)) := by
        gcongr
        · exact (diagL.trans l).trans (by nlinarith only [se.le] : E*S≤(E+1)*S)
        · exact (add_le_add_left (div_le_div_of_nonneg_right diagL rp.le) 1).trans div
      apply h1.trans
      have dg : 1≤D := d1
      calc
        _ ≤ ((E+1)*S)*G*((E+1)*(S/R))*(D*(8*(G+2))) := by
          apply le_mul_of_one_le_right (by positivity);nlinarith only [dg,g1,mul_le_mul_of_nonneg_left g1 (by positivity : 0≤D)]
        _ = _ := by ring
    · rw [pairBound,ite_eq_right eq]
      push_cast
      change (K.natAbs.divisors.card:ℝ)*(8*(Nat.log 2 (K.natAbs+2*B):ℝ)*(L/R+1))*(L*(harmonic B:ℝ)+B)≤_
      gcongr
      dsimp [D,K];linarith
  have poly : 8*G*(G+2) ≤ 32*(G+1)^2 := by nlinarith only [sq_nonneg G,g0]
  apply size.trans
  push_cast
  change _≤32*D*(E+1)^2*(G+1)^2*((lengthAt t:ℝ)/R)
  have iden : (lengthAt t:ℝ)=S^2 := by simp [lengthAt,S]
  rw [iden]
  calc _ = D*(E+1)^2*(S^2/R)*(8*G*(G+2)) := by ring
       _ ≤ D*(E+1)^2*(S^2/R)*(32*(G+1)^2) := by gcongr
       _ = _ := by ring

end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.flexible_pair
