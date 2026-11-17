import HeightTransfer
import PublicMargin

/-! A published integral Mordell estimate applies when one of the square
multipliers in the (4,4,3) descent is a unit. This module checks the numerical
specialization and the comparison with the public constant. -/
open ZInQ ZInQ.Mult ZInQBlueprint.OddSupport
namespace ZInQBlueprint.TwistDescent
noncomputable section

/-- A coarse integral consequence of von Känel, Corollary 7.4 and (7.2).
Here 62208=2^8*3^5 and the local quantity r₂(a) is bounded by |a|. -/
def MordellHeight : Prop :=
  ∀ (a X Y : ℤ), a≠0 → 0<X → Y^2=X^3+a →
    Real.log (X:ℝ) ≤ Real.log (a.natAbs:ℝ) +
      4*(62208*(a.natAbs:ℝ))*(Real.log (62208*(a.natAbs:ℝ)))^2

private theorem mordell_coarse (bound : MordellHeight) {a X Y : ℤ} (ha : a≠0) (hX : 0<X)
    (eq : Y^2=X^3+a) :
    Real.log (X:ℝ) ≤ (10:ℝ)^16*(a.natAbs:ℝ)^3 := by
  let A : ℝ := a.natAbs
  have a1 : 1≤A := by unfold A; exact_mod_cast (show 1≤a.natAbs from Int.natAbs_pos.mpr ha)
  have a0 : 0<A := by linarith
  have hlog := Real.log_le_sub_one_of_pos a0
  have bas : 1≤62208*A := by linarith
  have hlog2 := Real.log_le_sub_one_of_pos (by positivity : 0<62208*A)
  have q := pow_le_pow_left₀ (Real.log_nonneg bas) (show Real.log (62208*A)≤62208*A by linarith) 2
  have qq := mul_le_mul_of_nonneg_left q (show 0≤4*(62208*A) by positivity)
  have a3 : A≤A^3 := by nlinarith [mul_nonneg (show 0≤A-1 by linarith) (mul_nonneg a0.le (show 0≤A+1 by linarith))]
  have cube : 0≤A^3 := by positivity
  have b := bound a X Y ha hX eq
  change Real.log (X:ℝ) ≤ Real.log A + 4*(62208*A)*(Real.log (62208*A))^2 at b
  change Real.log (X:ℝ) ≤ (10:ℝ)^16 * A^3
  linarith only [b,hlog,qq,a3,cube]

/-- Two integral Mordell models. Choose the coefficient carrying the smaller
square multiplier. They work for arbitrary nonzero multipliers. -/
theorem mordell_models {r v m n T : ℤ} (sr : Squarefree r) (ss : Squarefree v)
    (mn : m≠0) (nn : n≠0) (tp : 0<T) (eq : r^2*m^4+27*v^2*n^4=T^3) :
    ∃ a X Y : ℤ, a≠0 ∧ 0<X ∧ Y^2=X^3+a ∧ T≤X ∧
      a.natAbs≤27*(r.natAbs*v.natAbs)^2*(min m.natAbs n.natAbs)^4 := by
  have r1 : 1≤r.natAbs := Int.natAbs_pos.mpr sr.ne_zero
  have s1 : 1≤v.natAbs := Int.natAbs_pos.mpr ss.ne_zero
  rcases le_total m.natAbs n.natAbs with h|h
  · refine ⟨-27*r^2*m^4,3*T,27*v*n^2,mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ sr.ne_zero)) (pow_ne_zero _ mn),
      by omega,?_,by omega,?_⟩
    · linear_combination 27*eq
    · rw [min_eq_left h]
      simp only [Int.natAbs_mul,Int.natAbs_pow,show (-27:ℤ).natAbs=27 by decide]
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simpa only [mul_one] using Nat.mul_le_mul_left r.natAbs s1
  · refine ⟨-27*v^2*n^4,T,r*m^2,mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ ss.ne_zero)) (pow_ne_zero _ nn),
      tp,?_,le_rfl,?_⟩
    · linear_combination eq
    · rw [min_eq_right h]
      simp only [Int.natAbs_mul,Int.natAbs_pow,show (-27:ℤ).natAbs=27 by decide]
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simpa only [one_mul] using Nat.mul_le_mul_right v.natAbs r1

/-- When one square multiplier is at most |d|, the published Mordell estimate
already yields the required public twist bound, with exponent 18 before padding. -/
theorem small_multiplier_height (bound : MordellHeight) {d k r v m n T : ℤ} {x : ℚ}
    (hd : d≠0) (sr : Squarefree r) (ss : Squarefree v) (mn : m≠0) (nn : n≠0)
    (hk : k=1 ∨ k=2) (norm : k^2*T=quadraticNorm x.num x.den)
    (eq : r^2*m^4+27*v^2*n^4=T^3) (div : r.natAbs*v.natAbs ∣ 30*d.natAbs)
    (small : min m.natAbs n.natAbs≤d.natAbs) :
    ratHeight x ≤ (10:ℝ)^31*(d.natAbs:ℝ)^18 := by
  obtain ⟨tp,_,hx⟩ := norm_height x hk norm
  obtain ⟨a,X,Y,ha,xp,mord,tx,ab⟩ := mordell_models sr ss mn nn tp eq
  have d1 : 1≤d.natAbs := Int.natAbs_pos.mpr hd
  have ds := Nat.le_of_dvd (Nat.mul_pos (by decide : 0<30) d1) div
  have as : a.natAbs≤24300*d.natAbs^6 := calc
    _ ≤ 27*(r.natAbs*v.natAbs)^2*(min m.natAbs n.natAbs)^4 := ab
    _ ≤ 27*(30*d.natAbs)^2*d.natAbs^4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ds _)) (Nat.pow_le_pow_left small _)
    _ = _ := by ring
  have aR : (a.natAbs:ℝ)≤24300*(d.natAbs:ℝ)^6 := by exact_mod_cast as
  have power := pow_le_pow_left₀ (Nat.cast_nonneg _ : (0:ℝ)≤a.natAbs) aR 3
  have h := mordell_coarse bound ha xp mord
  have ht := Real.log_le_log (show 0<(T:ℝ) by exact_mod_cast tp) (show (T:ℝ)≤(X:ℝ) by exact_mod_cast tx)
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have d18 : 1≤(d.natAbs:ℝ)^18 := one_le_pow₀ (by exact_mod_cast d1)
  linarith only [hx,ht,h,power,log2,d18]

/-- It suffices to bound the remaining primitive solutions where both square
multipliers exceed the twist. Only the stated published Mordell estimate is
used for points outside this set. -/
def LargeMultiplierBound (H : ℝ) : Prop :=
  ∀ (d r v m n T : ℤ), Squarefree d → Squarefree r → Squarefree v →
    r.natAbs.Coprime v.natAbs → m.natAbs.Coprime n.natAbs →
    r.natAbs*v.natAbs ∣ 30*d.natAbs → d.natAbs < min m.natAbs n.natAbs → 0<T →
    r^2*m^4+27*v^2*n^4=T^3 → Real.log (4*(T:ℝ)) ≤ 2*H*(d.natAbs:ℝ)^24

theorem sixContact_of_large_multipliers (published : MordellHeight)
    (remaining : LargeMultiplierBound publicTwistConstant) : SixContactMin := by
  apply sixContactMin_of_twistBound
  intro d x y sf ny _ point
  obtain ⟨k,r,v,m,n,T,hk,sr,ss,cr,mn,nn,cm,div,eq,norm,_⟩ := fermat_descent sf.ne_zero ny point
  by_cases small : min m.natAbs n.natAbs ≤ d.natAbs
  · have h := small_multiplier_height published sf.ne_zero sr ss mn nn hk norm eq div small
    have h1 : 1≤(d.natAbs:ℝ) := by exact_mod_cast (show 1≤d.natAbs from Int.natAbs_pos.mpr sf.ne_zero)
    have pub : (10:ℝ)^31 ≤ publicTwistConstant := (by norm_num : (10:ℝ)^31≤10^60).trans public_margin
    exact h.trans (mul_le_mul (by exact pub) (pow_le_pow_right₀ h1 (by decide : 18≤24))
      (by positivity) publicTwistConstant_pos.le)
  · obtain ⟨tp,_,hx⟩ := norm_height x hk norm
    have h := remaining d r v m n T sf sr ss cr cm div (lt_of_not_ge small) tp eq
    have four : Real.log (4:ℝ)=2*Real.log 2 := by
      simpa only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
    rw [Real.log_mul (by norm_num) (show (T:ℝ)≠0 by exact_mod_cast tp.ne'),four] at h
    linarith

#print axioms mordell_models
#print axioms small_multiplier_height
#print axioms sixContact_of_large_multipliers
end
end ZInQBlueprint.TwistDescent
