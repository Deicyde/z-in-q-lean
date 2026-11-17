import SumRemoved
import Mathlib.Analysis.SpecificLimits.Normed

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Filter
open scoped Classical
noncomputable section

/-- Along this sequence the manuscript's large-prime threshold is an exact integer. -/
def side (t : ℕ) := 2^(200*t)
def lengthAt (t : ℕ) := (side t)^2
def splitAt (t : ℕ) := 2^(2*t)

theorem side_pos (t : ℕ) : 0<side t := by dsimp [side];positivity
theorem length_pow (t : ℕ) : lengthAt t=2^(400*t) := by
  rw [lengthAt,side,←pow_mul]; congr 1;ring

def envelope (A : Fin 3→ℚ) : ℕ := 8*(maxCoefficient A+1)
def growth (C t : ℕ) : ℕ := C+401*t+2

theorem small_log (C t n : ℕ) (hn : n≤C*lengthAt t) :
    Nat.log 2 n ≤ growth C t ∧ Real.log (n:ℝ)≤growth C t := by
  have c : C≤2^C := (Nat.lt_pow_self (by decide : 1<2)).le
  have b : n≤2^(C+400*t) := by
    rw [pow_add,←length_pow];exact hn.trans (Nat.mul_le_mul_right _ c)
  have l := Nat.log_mono_right (b:=2) b
  rw [Nat.log_pow (by decide : 1<2)] at l
  constructor
  · dsimp [growth];omega
  · by_cases z : n=0
    · simp [z]
    have h:=Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero z) (show (n:ℝ)≤(2:ℝ)^(C+400*t) by exact_mod_cast b)
    rw [Real.log_pow] at h
    have two := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
    have le : Real.log 2≤1 := by linarith
    calc
      Real.log (n:ℝ)≤(C+400*t:ℕ)*Real.log 2 := h
      _ ≤ (C+400*t:ℕ) := by simpa using mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (C+400*t))
      _ ≤ (growth C t:ℝ) := by exact_mod_cast (show C+400*t≤growth C t by dsimp [growth];omega)

theorem radius_bounds (A : Fin 3→ℚ) (t V : ℕ) (v : V ≤ side t) (i j : ↥(shifts A)) :
    let S:=side t
    let N:=lengthAt t
    let E:=envelope A
    let b:=radius N V i j
    let a:=Nat.sqrt (N+(offset (dilation A) i.val).natAbs*V^2)
    a≤b ∧ 2*b+1≤E*S ∧ (gap i j*(V:ℤ)^2).natAbs+2*b≤E*N ∧
      a^2+1≤E*N ∧ N+maxCoefficient A*V^2+1≤E*N := by
  let S:=side t
  let N:=lengthAt t
  let C:=maxCoefficient A
  let c (i : ↥(shifts A)):=(offset (dilation A) i.val).natAbs
  let D:=max (c i) (c j)
  have cm (x : ↥(shifts A)) : c x≤C :=
    Finset.le_sup (f:=c) (Finset.mem_univ x)
  have dm : D≤C := max_le (cm _) (cm _)
  have s : 1≤S := side_pos _
  have ss : S≤N := by dsimp [N,lengthAt];change S≤S^2;nlinarith
  have vs : V^2≤N := Nat.pow_le_pow_left v 2
  have r : N+D*V^2≤((C+1)*S)^2 := calc
    _ ≤ N+C*N := Nat.add_le_add_left (Nat.mul_le_mul dm vs) _
    _ = (C+1)*S^2 := by change S^2+C*S^2=_;ring
    _ ≤ ((C+1)*S)^2 := by rw [mul_pow];exact Nat.mul_le_mul_right _ (by nlinarith : C+1≤(C+1)^2)
  have rb := Nat.sqrt_le_sqrt r
  rw [Nat.sqrt_eq'] at rb
  have g : (gap i j).natAbs≤2*C := by
    exact (Int.natAbs_sub_le _ _).trans (by dsimp [c] at cm;have := cm i; have := cm j; omega)
  have Kbound : (gap i j*(V:ℤ)^2).natAbs≤2*C*N := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using Nat.mul_le_mul g vs
  have asq : (Nat.sqrt (N+c i*V^2))^2≤N+C*N := (Nat.sqrt_le' _).trans (Nat.add_le_add_left (Nat.mul_le_mul (cm i) vs) _)
  have m : (C+1)*S≤(C+1)*N := Nat.mul_le_mul_left _ ss
  have sqN : 1≤N := s.trans ss
  have sqrtSmall := Nat.sqrt_le_sqrt (Nat.add_le_add_left (Nat.mul_le_mul_right (V^2) (le_max_left (c i) (c j))) N)
  let b:=Nat.sqrt (N+D*V^2)
  let a:=Nat.sqrt (N+c i*V^2)
  change a≤2*b ∧ 2*(2*b)+1≤8*(C+1)*S ∧
    (gap i j*(V:ℤ)^2).natAbs+2*(2*b)≤8*(C+1)*N ∧ a^2+1≤8*(C+1)*N ∧ N+C*V^2+1≤8*(C+1)*N
  change a≤b at sqrtSmall
  change b≤(C+1)*S at rb
  change a^2≤N+C*N at asq
  have xv := Nat.mul_le_mul_left C vs
  refine ⟨by omega,?_,?_,?_,?_⟩
  · nlinarith only [rb,s,Nat.zero_le (C*S)]
  · nlinarith only [Kbound,rb,m,Nat.zero_le (C*N),Nat.zero_le N]
  · nlinarith only [asq,sqN,Nat.zero_le (C*N)]
  · nlinarith only [xv,sqN,Nat.zero_le (C*N)]

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.small_log
#print axioms Sun28.SinglePrime.radius_bounds
