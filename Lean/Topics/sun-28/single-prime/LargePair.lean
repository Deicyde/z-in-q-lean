import DyadicWindows
import DivisorPower

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.SieveTail Sun28.SieveTail.Uniform
noncomputable section

def pairConstant (A : Fin 3→ℚ) : ℕ :=
  Finset.univ.sup (fun ij : ↥(shifts A)×↥(shifts A)=>divisorConstant 400*(gap ij.1 ij.2).natAbs+1)+1

theorem dyadic_scales (t : ℕ) :
    0<(splitAt t:ℝ) ∧ (splitAt t:ℝ)≤ side t ∧
    (2:ℝ)^t*((side t:ℝ)^2/(splitAt t))=(lengthAt t:ℝ)/(2:ℝ)^t := by
  have sr : (splitAt t:ℝ)=(2:ℝ)^(2*t) := by simp [splitAt]
  have sq : (splitAt t:ℝ) = ((2:ℝ)^t)^2 := by rw [sr,←pow_mul];congr 1;ring
  have lr : (lengthAt t:ℝ)=(side t:ℝ)^2 := by simp [lengthAt]
  refine ⟨by rw [sr];positivity,?_,?_⟩
  · exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (show 2*t≤200*t by omega))
  · rw [lr,sq];field_simp

theorem pair_power (A : Fin 3→ℚ) (t V : ℕ) (v : V ≤ side t) (i j : ↥(shifts A)) :
    (pairBound (lengthAt t) V (splitAt t) i j:ℝ) ≤
      (32*(pairConstant A:ℝ)*(envelope A+1:ℕ)^2)*(growth (envelope A) t+1:ℕ)^2*
        ((lengthAt t:ℝ)/(2:ℝ)^t) := by
  let S : ℝ := side t
  let E : ℝ := envelope A
  let G : ℝ := growth (envelope A) t
  let D : ℝ := pairConstant A
  let R : ℝ := splitAt t
  let B := radius (lengthAt t) V i j
  let a:=Nat.sqrt (lengthAt t+(offset (dilation A) i.val).natAbs*V^2)
  let K:=gap i j*(V:ℤ)^2
  let L : ℝ := 2*B+1
  obtain ⟨ab,lmax,kmax,amax,_⟩:=radius_bounds A t V v i j
  have l : L≤E*S := by dsimp only [L,E,S,B];exact_mod_cast lmax
  have diagL : 2*(a:ℝ)+1≤L := by dsimp only [L];exact_mod_cast (by omega : 2*a+1≤2*B+1)
  have ⟨rp,rs,iden⟩:=dyadic_scales t
  have se : 0<S := by dsimp [S];exact_mod_cast side_pos t
  have e0 : 0≤E := Nat.cast_nonneg _
  have g0 : 0≤G := Nat.cast_nonneg _
  have g1 : 1≤G := by dsimp [G];exact_mod_cast (by dsimp [growth];omega : 1≤growth (envelope A) t)
  have d1 : 1≤D := by dsimp [D,pairConstant];exact_mod_cast (Nat.le_add_left 1 _)
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
  have tpos : (1:ℝ)≤2^t := one_le_pow₀ (by norm_num)
  have tau:=tau_row (gap i j) t V v
  have lim:=Finset.le_sup (f:=fun ij : ↥(shifts A)×↥(shifts A)=>divisorConstant 400*(gap ij.1 ij.2).natAbs+1) (Finset.mem_univ (i,j))
  have tc : (K.natAbs.divisors.card:ℝ) ≤ D*2^t := by
    dsimp only [K,D,pairConstant];exact_mod_cast tau.trans (Nat.mul_le_mul_right _ (lim.trans (Nat.le_succ _)))
  have lgk : (Nat.log 2 (K.natAbs+2*B):ℝ)≤G := by dsimp [G,B,K];exact_mod_cast (small_log _ t _ kmax).1
  have lga : (Nat.log 2 (a^2+1):ℝ)≤G := by dsimp [G,a];exact_mod_cast (small_log _ t _ amax).1
  have size : (pairBound (lengthAt t) V (splitAt t) i j:ℝ) ≤
      (D*2^t)*(8*G*((E+1)*(S/R)))*((E+1)*S*(G+2)) := by
    by_cases eq : i=j
    · rw [pairBound,ite_eq_left eq]
      push_cast
      have h1 : (2*(a:ℝ)+1)*(Nat.log 2 (a^2+1):ℝ)*( (2*(a:ℝ)+1)/R+1) ≤
          ( (E+1)*S)*G*((E+1)*(S/R)) := by
        gcongr
        · exact (diagL.trans l).trans (by nlinarith only [se.le] : E*S≤(E+1)*S)
        · exact (add_le_add_left (div_le_div_of_nonneg_right diagL rp.le) 1).trans div
      apply h1.trans
      have dg : 1≤D*2^t := one_le_mul_of_one_le_of_one_le d1 tpos
      calc
        _ ≤ ((E+1)*S)*G*((E+1)*(S/R))*((D*2^t)*(8*(G+2))) := by
          apply le_mul_of_one_le_right (by positivity);nlinarith only [dg,g1,mul_le_mul_of_nonneg_left g1 (by positivity : 0≤D*2^t)]
        _ = _ := by ring
    · rw [pairBound,ite_eq_right eq]
      push_cast
      change (K.natAbs.divisors.card:ℝ)*(8*(Nat.log 2 (K.natAbs+2*B):ℝ)*(L/R+1))*(L*(harmonic B:ℝ)+B)≤_
      gcongr
  have poly : 8*G*(G+2) ≤ 32*(G+1)^2 := by nlinarith only [sq_nonneg G,g0]
  apply size.trans
  push_cast
  change _≤32*D*(E+1)^2*(G+1)^2*((lengthAt t:ℝ)/(2:ℝ)^t)
  rw [←iden]
  calc _ = D*(E+1)^2*((2:ℝ)^t*(S^2/R))*(8*G*(G+2)) := by ring
       _ ≤ D*(E+1)^2*(2^t*(S^2/R))*(32*(G+1)^2) := by gcongr
       _ = _ := by ring

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.dyadic_scales
#print axioms Sun28.SinglePrime.pair_power
