import OmegaWeights
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A symbolic induction gives a bound uniform in the exponent and the integer cutoff. -/
namespace ZInQBlueprint.TwistCount
open Finset
open scoped Classical
noncomputable section

/-- Reverse the order of summation over positive d | m ≤ K. -/
theorem divisor_box (K : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 K, ∑ d ∈ m.divisors, f d) =
      ∑ u ∈ Icc 1 K, ∑ d ∈ Icc 1 (K/u), f d := by
  let I:=Icc 1 K
  let lhs := I.sigma fun m=>m.divisors
  let rhs := I.sigma fun u=>Icc 1 (K/u)
  rw [sum_sigma' (Icc 1 K) (fun m=>m.divisors) (fun _ d=>f d),
      sum_sigma' (Icc 1 K) (fun u=>Icc 1 (K/u)) (fun _ d=>f d)]
  change ∑ x ∈ lhs, f x.2 = ∑ x ∈ rhs, f x.2
  apply sum_bij' (fun x _ => (⟨x.1/x.2,x.2⟩ : Sigma (fun _ : ℕ => ℕ)))
    (fun x _ => (⟨x.1*x.2,x.2⟩ : Sigma (fun _ : ℕ => ℕ)))
  · intro x hx
    obtain ⟨mx,dx⟩:=mem_sigma.mp hx
    have mp := (mem_Icc.mp mx).1
    have dp:=Nat.pos_of_mem_divisors dx
    have dvd:=Nat.dvd_of_mem_divisors dx
    have prod:=Nat.div_mul_cancel dvd
    have up : 0<x.1/x.2 := Nat.div_pos (Nat.le_of_dvd mp dvd) dp
    change (⟨x.1/x.2,x.2⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ rhs
    apply mem_sigma.mpr
    change x.1/x.2∈Icc 1 K ∧ x.2∈Icc 1 (K/(x.1/x.2))
    refine ⟨mem_Icc.mpr ⟨up,(Nat.div_le_self ..).trans (mem_Icc.mp mx).2⟩,
      mem_Icc.mpr ⟨dp,(Nat.le_div_iff_mul_le up).mpr ?_⟩⟩
    rw [Nat.mul_comm,prod]
    exact (mem_Icc.mp mx).2
  · intro x hx
    obtain ⟨up,dp⟩:=mem_sigma.mp hx
    obtain ⟨pu,_⟩:=mem_Icc.mp up
    obtain ⟨pd,bd⟩:=mem_Icc.mp dp
    have mpos:=Nat.mul_pos pu pd
    apply mem_sigma.mpr
    change x.1*x.2∈Icc 1 K ∧ x.2∈(x.1*x.2).divisors
    refine ⟨mem_Icc.mpr ⟨mpos,?_⟩,Nat.mem_divisors.mpr ⟨dvd_mul_left ..,mpos.ne'⟩⟩
    simpa only [Nat.mul_comm x.2] using (Nat.le_div_iff_mul_le pu).mp bd
  · intro x hx
    rcases x with ⟨m,d⟩
    have h := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
    change (⟨m/d*d,d⟩ : Sigma (fun _ : ℕ => ℕ))=⟨m,d⟩
    rw [show m/d*d=m from h]
  · intro x hx
    rcases x with ⟨u,d⟩
    have dp : 0<d := (mem_Icc.mp (mem_sigma.mp hx).2).1
    change (⟨u*d/d,d⟩ : Sigma (fun _ : ℕ => ℕ))=⟨u,d⟩
    rw [Nat.mul_div_cancel _ dp]
  · intros; rfl

/-- Includes K=0. No estimate requires enumerating n colors. -/
theorem sum_omega (n K : ℕ) :
    (∑ m ∈ Icc 1 K, (((n+1)^omega m:ℕ):ℝ)) ≤
      (K:ℝ)*(1+Real.log (K:ℝ))^n := by
  induction n generalizing K with
  | zero => simp [Nat.card_Icc]
  | succ n ih =>
    by_cases zero:K=0
    · simp [zero]
    have kp := Nat.pos_of_ne_zero zero
    let H:=1+Real.log (K:ℝ)
    have core : 0≤Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast kp)
    have hn : 0≤H := by dsimp [H];linarith
    have step (u : ℕ) (hu:u∈Icc 1 K) :
        ∑ d ∈ Icc 1 (K/u), (((n+1)^omega d:ℕ):ℝ) ≤ ((K:ℝ)*H^n)*(u:ℝ)⁻¹ := by
      obtain ⟨up,uc⟩:=mem_Icc.mp hu
      have positive : 0<K/u := Nat.div_pos uc up
      have ratio : ((K/u:ℕ):ℝ) ≤ (K:ℝ)/(u:ℝ) := by
        apply (le_div_iff₀ (by exact_mod_cast up : (0:ℝ)<u)).mpr
        exact_mod_cast Nat.div_mul_le_self K u
      have small : 1+Real.log ((K/u:ℕ):ℝ) ≤ H := by
        dsimp [H]
        exact add_le_add_right (Real.log_le_log (by exact_mod_cast positive : (0:ℝ)<((K/u:ℕ):ℝ))
          (by exact_mod_cast Nat.div_le_self K u : ((K/u:ℕ):ℝ)≤K)) _
      have rest : 0 ≤ 1+Real.log ((K/u:ℕ):ℝ) :=
        add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast positive))
      calc
        _ ≤ _ := ih (K/u)
        _ ≤ ((K:ℝ)/(u:ℝ))*H^n := mul_le_mul ratio (pow_le_pow_left₀ rest small n)
          (pow_nonneg rest _) (by positivity)
        _ = _ := by rw [div_eq_mul_inv];ring
    have harm : (∑ i ∈ Icc 1 K, (i:ℝ)⁻¹) = (harmonic K:ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    calc
      _ ≤ ∑ m ∈ Icc 1 K, ∑ d ∈ m.divisors, (((n+1)^omega d:ℕ):ℝ) := by
        apply sum_le_sum
        intro m hm
        exact_mod_cast add_weight_le_divisors (n+1) m (Nat.ne_of_gt (mem_Icc.mp hm).1)
      _ = _ := divisor_box K _
      _ ≤ ∑ i ∈ Icc 1 K, ((K:ℝ)*H^n)*(i:ℝ)⁻¹ := sum_le_sum step
      _ = ((K:ℝ)*H^n)*(harmonic K:ℝ) := by rw [←mul_sum,harm]
      _ ≤ ((K:ℝ)*H^n)*H := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hn _))
      _ = _ := by dsimp [H];rw [pow_succ,mul_assoc]

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.divisor_box
#print axioms ZInQBlueprint.TwistCount.sum_omega
