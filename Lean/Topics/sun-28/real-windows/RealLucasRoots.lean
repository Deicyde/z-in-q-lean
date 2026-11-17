import RealWitnessWindows
import ZInQKernel.Compiler.Exponential.AlphaParameterCongruence
import ZInQKernel.Compiler.Exponential.AlphaGrowth

/-! The least preceding Lucas neighbor suffices for the odd positive target.
With s=6k+7 take d=s-2=6k+5, z=U_d/d and t=U_(d-1). -/
namespace Sun28.RealWindows
open ZInQ.AlphaPower Sun28.Ordinary

private theorem parity_period (s k : ℕ) (odd : s % 2 =1) :
    alphaZ s (3*k) % 2 =0 ∧ alphaZ s (3*k+1) % 2 =1 ∧ alphaZ s (3*k+2) % 2 =1 := by
  have so : (s:ℤ) % 2 =1 := by omega
  have step (j : ℕ) (u v : ℤ) (hu : alphaZ s j % 2 =u) (hv : alphaZ s (j+1) % 2 =v) :
      alphaZ s (j+2) % 2 =(v-u) % 2  := by
    rw [alphaZ_add_two,Int.sub_emod,Int.mul_emod,so,hu,hv]
    omega
  induction k with
  | zero =>
    have a := step 0 0 1 (by simp [alphaZ_zero]) (by simp [alphaZ_one])
    simpa [alphaZ_zero,alphaZ_one] using
      (show alphaZ s 0 % 2 =0 ∧ alphaZ s 1 % 2 =1 ∧ alphaZ s (0+2) % 2 =1 from
        ⟨by simp [alphaZ_zero],by simp [alphaZ_one],by simpa using a⟩)
  | succ k ih =>
    obtain ⟨_,b,c⟩:=ih
    have d := step (3*k+1) 1 1 b c
    have e := step (3*k+2) 1 0 c (by simpa using d)
    have f := step (3*k+3) 0 1 (by simpa using d) (by simpa using e)
    norm_num at d e f
    simpa [Nat.mul_succ,Nat.add_assoc] using And.intro d (And.intro e f)

/-- For the scalar congruence s=1 mod 6, the indices d-1,d already give two
odd positive witnesses. Sun uses indices 2d,2d+1. -/
theorem short_lucas_roots (k : ℕ) :
    let s : ℕ:=6*k+7
    let d : ℕ:=6*k+5
    let t:=alphaZ s (d-1)
    let z:=alphaZ s d/(d:ℤ)
    0<t ∧ 0<z ∧ Odd t ∧ Odd z ∧ lucas (s:ℤ) t z=0 := by
  dsimp only
  let s := 6*k+7
  let d := 6*k+5
  have sd : (s:ℤ)-2=(d:ℤ) := by dsimp [s,d];ring
  have dp : (0:ℤ)<d := by dsimp [d];omega
  have dno : (d:ℤ)≠0 := ne_of_gt dp
  have c : s ≡ 2 [MOD d] := by
    change (d+2)%d=2%d
    simp
  have v := alphaZ_modEq_index (d:=d) c d
  change alphaZ s d%(d:ℤ)=(d:ℤ)%(d:ℤ) at v
  rw [Int.emod_self] at v
  have dvd := Int.dvd_of_emod_eq_zero v
  have zval := Int.ediv_mul_cancel dvd
  have pair:=parity_period s (2*k+1) (by dsimp [s];omega)
  have i1 : d-1=3*(2*k+1)+1 := by dsimp [d];omega
  have i2 : d=3*(2*k+1)+2 := by dsimp [d];omega
  have tOdd : Odd (alphaZ s (d-1)) := Int.odd_iff.mpr (i1 ▸ pair.2.1)
  have uOdd : Odd (alphaZ s d) := Int.odd_iff.mpr (i2 ▸ pair.2.2)
  have zOdd : Odd (alphaZ s d/(d:ℤ)) := (Int.odd_mul.mp (zval ▸ uOdd) |>.1)
  have tp := alphaZ_pos s (by dsimp [s];omega) (n:=d-1) (by dsimp [d];omega)
  have up := alphaZ_pos s (by dsimp [s];omega) (n:=d) (by dsimp [d];omega)
  have zp : 0<alphaZ s d/(d:ℤ) := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h dp.le
    rw [zval] at this
    omega
  have eq:=alphaZ_cassini s (d-1)
  rw [show d-1+1=d by omega] at eq
  refine ⟨tp,zp,tOdd,zOdd,?_⟩
  unfold lucas
  rw [sd]
  rw [←zval] at eq
  linear_combination eq

end Sun28.RealWindows
#print axioms Sun28.RealWindows.short_lucas_roots
