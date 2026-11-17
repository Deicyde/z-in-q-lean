import PublicTwistHeight
import ZInQKernel.Main

/-! A numerical lower bound for the sufficient coefficient in the public
twist estimate. Only the sizes of the prime set and of D enter the comparison. -/
open ZInQ ZInQ.Mult ZInQBlueprint.OddSupport
namespace ZInQBlueprint.TwistDescent
noncomputable section

private theorem integer_margin (D E : ℕ) (S : Finset ℕ) (hD : 10^12≤D) (e0 : 100≤E)
    (small : ∀ p ∈ S, p≤D) : (10^60:ℕ)*(∏ p ∈ S,p)^24 ≤ D^(D*E) := by
  let P := ∏ p ∈ S, p
  have d1 : 1≤D := by omega
  have sub : S ⊆ Finset.range (D+1) := fun p hp =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (small p hp))
  have card : S.card ≤ D+1 := by simpa using Finset.card_le_card sub
  have pd : P≤D^(D+1) := calc
    P ≤ ∏ _p ∈ S, D := Finset.prod_le_prod (fun p hp => small p hp)
    _ = D^S.card := by simp
    _ ≤ D^(D+1) := Nat.pow_le_pow_right d1 card
  have ex : 5+(D+1)*24 ≤ D*E := by
    have le := Nat.mul_le_mul_left D e0
    omega
  have d5 : (10^60:ℕ) ≤ D^5 := calc
    (10^60:ℕ) = (10^12)^5 := by decide
    _ ≤ D^5 := Nat.pow_le_pow_left hD 5
  change (10^60:ℕ)*P^24 ≤ D^(D*E)
  calc
    _ ≤ D^5*(D^(D+1))^24 := Nat.mul_le_mul d5 (Nat.pow_le_pow_left pd 24)
    _ = D^(5+(D+1)*24) := by rw [pow_add D 5 ((D+1)*24),pow_mul D (D+1) 24]
    _ ≤ D^(D*E) := Nat.pow_le_pow_right d1 ex

private theorem exponent_size (D G : ℕ) (d1 : 1≤D) (g : 10≤G) : 100≤10*(D*G)^2 := by
  have a : 10≤D*G := le_trans g (by simpa only [one_mul] using Nat.mul_le_mul_right G d1)
  nlinarith

private theorem real_margin (D E P : ℕ) (C : ℝ) (d1 : 1≤D) (p0 : 0<P)
    (scale : (10^60:ℕ)*P^24 ≤ D^(D*E)) :
    (10:ℝ)^60 ≤
      (2*10^13*max 1 (max C (((D:ℝ)^((D:ℝ)*(E:ℝ)))^17))-Real.log 1800)/(P:ℝ)^24 := by
  let Q : ℝ := (D:ℝ)^((D:ℝ)*(E:ℝ))
  have eq : Q=(D:ℝ)^(D*E) := by
    unfold Q
    rw [←Nat.cast_mul,Real.rpow_natCast]
  have lower : (10:ℝ)^60*(P:ℝ)^24 ≤ Q := by
    rw [eq]
    exact_mod_cast scale
  have q1 : 1≤Q := by rw [eq]; exact one_le_pow₀ (by exact_mod_cast d1)
  have hq := le_trans (le_max_right C (Q^17)) (le_max_right (1:ℝ) (max C (Q^17)))
  have q17 : Q ≤ Q^17 := by simpa only [pow_one] using (pow_le_pow_right₀ q1 (by decide : 1≤17))
  have log := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1800)
  have ppos : 0<(P:ℝ) := by exact_mod_cast p0
  change (10:ℝ)^60 ≤ (2*10^13*max 1 (max C (Q^17))-Real.log 1800)/(P:ℝ)^24
  apply (le_div_iff₀ (pow_pos ppos _)).mpr
  linarith only [lower,q17,hq,q1,log]

private theorem public_d_one : 1≤heightD :=
  le_trans (by decide : 1≤10^12) Compiler.Precision.ten_pow_twelve_le_heightD

private theorem public_exponent : 100≤heightE0 := by
  rw [Compiler.Precision.heightE0_eq]
  exact exponent_size heightD heightG0 public_d_one (by decide)

private theorem public_integer_margin :
    (10^60:ℕ)*(∏ p ∈ S_mul,p)^24 ≤ heightD^(heightD*heightE0) :=
  integer_margin heightD heightE0 S_mul Compiler.Precision.ten_pow_twelve_le_heightD public_exponent
    (fun _ hp => le_heightD_of_mem_S_mul hp)

private theorem public_real_margin :
    (10:ℝ)^60 ≤
      (2*10^13*max 1 (max (heightCcm:ℝ) (((heightD:ℝ)^((heightD:ℝ)*(heightE0:ℝ)))^17))-
       Real.log 1800)/((∏ p ∈ S_mul,p : ℕ):ℝ)^24 := by
  have big : 10^12 ≤ heightD := Compiler.Precision.ten_pow_twelve_le_heightD
  have d1 : 1≤heightD := le_trans (by decide : 1≤10^12) big
  have ppos : 0<∏ p ∈ S_mul,p := Finset.prod_pos (fun p hp => (prime_of_mem_S_mul hp).pos)
  exact real_margin heightD heightE0 (∏ p ∈ S_mul,p) (heightCcm:ℝ) d1 ppos public_integer_margin

theorem public_margin : (10:ℝ)^60 ≤ publicTwistConstant := by
  unfold publicTwistConstant heightH6 heightQ
  exact public_real_margin

#print axioms public_margin
end
end ZInQBlueprint.TwistDescent
