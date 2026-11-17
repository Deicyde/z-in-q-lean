import FermatDescent
import PublicTwistHeight

/-! Archimedean comparison with the cubic norm T and a sufficient bound
on primitive weighted (4,4,3) solutions. -/
open ZInQ ZInQBlueprint.OddSupport
namespace ZInQBlueprint.TwistDescent
noncomputable section

/-- The normalized quadratic norm recovers the abscissa height within log 2
on either side, uniformly in the twist. -/
theorem norm_height (x : ℚ) {k T : ℤ} (hk : k=1 ∨ k=2)
    (eq : k^2*T=quadraticNorm x.num x.den) :
    0<T ∧ Real.log (T:ℝ)/2-Real.log 2 ≤ ratHeight x ∧
      ratHeight x ≤ Real.log (T:ℝ)/2+Real.log 2 := by
  let M : ℝ := max |(x.num:ℝ)| (x.den:ℝ)
  have b : (0:ℝ)<x.den := by exact_mod_cast x.den_pos
  have mp : 0<M := b.trans_le (le_max_right _ _)
  have comparison : M^2 ≤ (x.num:ℝ)^2+3*(x.den:ℝ)^2 ∧
        (x.num:ℝ)^2+3*(x.den:ℝ)^2 ≤ 4*M^2 := by
    have ab := sq_abs (x.num:ℝ)
    by_cases am : |(x.num:ℝ)|≤(x.den:ℝ)
    · rw [show M=(x.den:ℝ) from max_eq_right am]
      have := pow_le_pow_left₀ (abs_nonneg _) am 2
      constructor <;> nlinarith [sq_nonneg (x.num:ℝ),sq_nonneg (x.den:ℝ)]
    · rw [show M=|(x.num:ℝ)| from max_eq_left (le_of_not_ge am)]
      have := pow_le_pow_left₀ b.le (le_of_not_ge am) 2
      constructor <;> nlinarith [sq_nonneg (x.den:ℝ)]
  have eqR : (k:ℝ)^2*(T:ℝ)=(x.num:ℝ)^2+3*(x.den:ℝ)^2 := by
    exact_mod_cast eq
  have ltM : 0<M^2 := sq_pos_of_pos mp
  have bounds : 0<(T:ℝ) ∧ M^2≤4*(T:ℝ) ∧ (T:ℝ)≤4*M^2 := by
    rcases hk with h|h <;> rw [h] at eqR <;> norm_num at eqR <;>
      constructor <;> (first | constructor <;> linarith [comparison.1,comparison.2] | linarith [comparison.1])
  obtain ⟨tp,lo,hi⟩ := bounds
  have l := Real.log_le_log ltM lo
  have h := Real.log_le_log tp hi
  have four : Real.log (4:ℝ)=2*Real.log 2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
  rw [Real.log_mul (by norm_num) tp.ne',Real.log_pow,four] at l
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ mp.ne'),Real.log_pow,four] at h
  change 0<T ∧ _ ≤ Real.log M ∧ Real.log M ≤ _
  exact ⟨by exact_mod_cast tp,by push_cast at h; linarith,by push_cast at l; linarith⟩

def Primitive443Bound (C : ℝ) : Prop :=
  ∀ (r s m n T : ℤ), Squarefree r → Squarefree s → r.natAbs.Coprime s.natAbs →
    m ≠ 0 → n ≠ 0 → m.natAbs.Coprime n.natAbs → 0<T →
    r^2*m^4 + 27*s^2*n^4 = T^3 →
    Real.log (4*(T:ℝ)) ≤ C*((r.natAbs:ℝ)*(s.natAbs:ℝ))^24

theorem twists_of_primitive443 {C : ℝ} (h : 0≤C) (bound : Primitive443Bound C) :
    TwistBound (C*30^24/2) := by
  intro d x y sf ny _ point
  obtain ⟨k,r,s,m,n,T,hk,sr,ss,cr,mn,nn,cm,div,eq,norm,_⟩ :=
    fermat_descent sf.ne_zero ny point
  obtain ⟨tp,_,hx⟩ := norm_height x hk norm
  have hT : (0:ℝ)<T := by exact_mod_cast tp
  have bh := bound r s m n T sr ss cr mn nn cm tp eq
  have pd := Int.natAbs_pos.mpr sf.ne_zero
  have dd : (r.natAbs:ℝ)*(s.natAbs:ℝ)≤30*(d.natAbs:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by decide : 0<30) pd) div
  have kp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) dd 24) h
  have four : Real.log (4:ℝ)=2*Real.log 2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
  rw [Real.log_mul (by norm_num) hT.ne',four] at bh
  rw [mul_pow] at kp
  linarith only [hx,bh,kp]

theorem sixContact_of_primitive443
    (bound : Primitive443Bound (2*publicTwistConstant/30^24)) : SixContactMin := by
  apply sixContactMin_of_twistBound
  have p := publicTwistConstant_pos
  have h := twists_of_primitive443 (show 0≤2*publicTwistConstant/30^24 by positivity) bound
  convert h using 1
  ring

#print axioms norm_height
#print axioms twists_of_primitive443
#print axioms sixContact_of_primitive443
end
end ZInQBlueprint.TwistDescent
