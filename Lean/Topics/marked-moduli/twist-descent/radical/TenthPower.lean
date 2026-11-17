import CappedRadical

/-! Height bound with the square multipliers at most the tenth power of the
signed twisting parameter; the complement is the only remaining quartic case. -/
open UniqueFactorizationMonoid ZInQ ZInQBlueprint.OddSupport
namespace ZInQBlueprint.TwistDescent
noncomputable section

private theorem real_envelope {D A B X : ℝ} (d1 : 1≤D) (a0 : 0<A) (b1 : 1≤B)
    (ac : A≤24300*D^42) (bc : B≤10^9*D^22)
    (est : Real.log X ≤ Real.log A+4*B*(Real.log B)^2) :
    Real.log X ≤ 10^29*D^24 := by
  have d0 : 0<D := by linarith
  have ld := Real.log_le_sub_one_of_pos d0
  have la := Real.log_le_log a0 ac
  have lb := Real.log_le_log (by linarith) bc
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ d0.ne'),Real.log_pow D 42] at la
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ d0.ne'),Real.log_pow D 22] at lb
  have cA := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<24300)
  have cB := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10^9)
  have logA : Real.log A ≤ 25000*D := by push_cast at la; linarith
  have logB : Real.log B ≤ (10^9+22)*D := by push_cast at lb; linarith
  have powB := pow_le_pow_left₀ (Real.log_nonneg b1) logB 2
  have prod := mul_le_mul bc powB (sq_nonneg _) (by positivity : 0≤10^9*D^22)
  have d24 : D≤D^24 := by simpa only [pow_one] using pow_le_pow_right₀ d1 (by decide : 1≤24)
  linarith only [est,logA,prod,d24,show 0≤D^24 by positivity]

/-- Effective exponent-ten sector, from r₂(a) rather than |a| in Corollary 7.4. -/
theorem tenth_power_height (published : IntegralMordell74)
    {d k r v m n T : ℤ} {x : ℚ} (hd : d≠0) (sr : Squarefree r) (sv : Squarefree v)
    (mn : m≠0) (nn : n≠0) (hk : k=1 ∨ k=2) (norm : k^2*T=quadraticNorm x.num x.den)
    (eq : r^2*m^4+27*v^2*n^4=T^3) (div : r.natAbs*v.natAbs ∣ 30*d.natAbs)
    (small : min m.natAbs n.natAbs ≤ d.natAbs^10) :
    ratHeight x ≤ (10:ℝ)^29*(d.natAbs:ℝ)^24 := by
  obtain ⟨tp,_,hx⟩ := norm_height x hk norm
  obtain ⟨u,l,X,Y,un,ln,xp,tx,meq,ub,leq⟩ := selected_mordell sr sv mn nn tp eq
  let D := d.natAbs
  let a := -27*u^2*l^4
  have d1 : 1≤D := Int.natAbs_pos.mpr hd
  have us : u.natAbs ≤ 30*D := ub.trans (Nat.le_of_dvd (Nat.mul_pos (by decide : 0<30) d1) div)
  have ls : l.natAbs ≤ D^10 := leq ▸ small
  have an : a≠0 := mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ un)) (pow_ne_zero _ ln)
  have ac : a.natAbs≤24300*D^42 := calc
    _ = 27*u.natAbs^2*l.natAbs^4 := by simp only [a,Int.natAbs_mul,Int.natAbs_pow,show (-27:ℤ).natAbs=27 by decide]
    _ ≤ 27*(30*D)^2*(D^10)^4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left us _)) (Nat.pow_le_pow_left ls _)
    _ = _ := by ring
  have ur := (Nat.radical_le_self_iff.mpr (Int.natAbs_ne_zero.mpr un)).trans us
  have lr := (Nat.radical_le_self_iff.mpr (Int.natAbs_ne_zero.mpr ln)).trans ls
  have bc : 62208*cappedPart a.natAbs ≤ 10^9*D^22 := calc
    _ ≤ 62208*(9*(radical u.natAbs)^2*(radical l.natAbs)^2) :=
      Nat.mul_le_mul_left 62208 (capped_mordell_radical u l)
    _ ≤ 62208*(9*(30*D)^2*(D^10)^2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ur _)) (Nat.pow_le_pow_left lr _))
    _ = 503884800*D^22 := by ring
    _ ≤ 10^9*D^22 := Nat.mul_le_mul_right _ (by decide)
  have bounds := published a X Y an xp meq
  have rx := real_envelope (D:=(D:ℝ)) (by exact_mod_cast d1)
    (by exact_mod_cast Int.natAbs_pos.mpr an : (0:ℝ)<a.natAbs)
    (show (1:ℝ)≤62208*(cappedPart a.natAbs:ℝ) by
      have h : (1:ℝ)≤cappedPart a.natAbs := by exact_mod_cast (show 1≤cappedPart a.natAbs from cappedPart_pos _)
      linarith)
    (by exact_mod_cast ac) (by exact_mod_cast bc) bounds
  have ht := Real.log_le_log (show 0<(T:ℝ) by exact_mod_cast tp) (show (T:ℝ)≤(X:ℝ) by exact_mod_cast tx)
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have d24 : (1:ℝ)≤(D:ℝ)^24 := one_le_pow₀ (by exact_mod_cast d1)
  change ratHeight x≤10^29*(D:ℝ)^24
  linarith only [hx,ht,rx,log2,d24]

def AboveTenthPower (H : ℝ) : Prop :=
  ∀ (d r v m n T : ℤ), Squarefree d → Squarefree r → Squarefree v →
    r.natAbs.Coprime v.natAbs → m.natAbs.Coprime n.natAbs →
    r.natAbs*v.natAbs ∣ 30*d.natAbs → d.natAbs^10 < min m.natAbs n.natAbs → 0<T →
    r^2*m^4+27*v^2*n^4=T^3 → Real.log (4*(T:ℝ)) ≤ 2*H*(d.natAbs:ℝ)^24

theorem sixContact_of_above_tenth_power (published : IntegralMordell74)
    (remaining : AboveTenthPower publicTwistConstant) : SixContactMin := by
  apply sixContactMin_of_twistBound
  intro d x y sf ny _ point
  obtain ⟨k,r,v,m,n,T,hk,sr,sv,cr,mn,nn,cm,div,eq,norm,_⟩ := fermat_descent sf.ne_zero ny point
  by_cases small : min m.natAbs n.natAbs ≤ d.natAbs^10
  · have h := tenth_power_height published sf.ne_zero sr sv mn nn hk norm eq div small
    have margin : (10:ℝ)^29≤publicTwistConstant := (by norm_num : (10:ℝ)^29≤10^60).trans public_margin
    exact h.trans (mul_le_mul_of_nonneg_right margin (by positivity))
  · obtain ⟨tp,_,hx⟩ := norm_height x hk norm
    have h := remaining d r v m n T sf sr sv cr cm div (lt_of_not_ge small) tp eq
    have four : Real.log (4:ℝ)=2*Real.log 2 := by
      simpa only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] using Real.log_pow (2:ℝ) 2
    rw [Real.log_mul (by norm_num) (show (T:ℝ)≠0 by exact_mod_cast tp.ne'),four] at h
    linarith

#print axioms tenth_power_height
#print axioms sixContact_of_above_tenth_power
end
end ZInQBlueprint.TwistDescent
