import MordellSupport
import TenthPower

/-! The two Mordell equations for the primitive cubic coordinates, after rescaling.
Only the primes of the chosen coordinate control the upper bound. -/
open ZInQ ZInQBlueprint.OddSupport UniqueFactorizationMonoid
namespace ZInQBlueprint.TwistDescent
noncomputable section

private theorem real_envelope {D A B X : ℝ} (d1 : 1≤D) (a0 : 0<A) (b1 : 1≤B)
    (ac : A≤10^8*D^44) (bc : B≤10^9*D^22)
    (est : X ≤ Real.log A+4*B*(Real.log B)^2) :
    X ≤ 10^29*D^24 := by
  have d0 : 0<D := by linarith
  have ld := Real.log_le_sub_one_of_pos d0
  have la := Real.log_le_log a0 ac
  have lb := Real.log_le_log (by linarith) bc
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ d0.ne'),Real.log_pow D 44] at la
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ d0.ne'),Real.log_pow D 22] at lb
  have ca := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10^8)
  have cb := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10^9)
  have logA : Real.log A ≤ (10^8+44)*D := by push_cast at la; linarith
  have logB : Real.log B ≤ (10^9+22)*D := by push_cast at lb; linarith
  have p := pow_le_pow_left₀ (Real.log_nonneg b1) logB 2
  have q := mul_le_mul bc p (sq_nonneg _) (by positivity : 0≤10^9*D^22)
  have d24 : D≤D^24 := by simpa only [pow_one] using pow_le_pow_right₀ d1 (by decide : 1≤24)
  linarith only [est,logA,q,d24,show 0≤D^24 by positivity]

/-- Height of a primitive model with a bound only on the radical of w. -/
theorem support_mordell_height (published : SupportedMordell74)
    {D Z w v c : ℕ} (d1 : 1≤D) (zp : 0<Z) (wp : 0<w) (cw : w.Coprime v)
    (cp : 0<c) (c27 : c≤27) (eqn : Z^3=(c*v)^2+27*w^2)
    (small : radical w ≤ 30*D^11) :
    Real.log (Z:ℝ) ≤ 10^30*(D:ℝ)^24 := by
  obtain ⟨k,e,kp,ep,fac,er⟩ := remove_cubes w wp
  have kd : k^2 ∣ w := ⟨k*e,by rw [fac]; ring⟩
  have kw : k ∣ w := (dvd_pow_self k (by decide : 2≠0)).trans kd
  have ed : e ∣ w := ⟨k^3,by simpa only [mul_comm] using fac⟩
  let S := (3*w).primeFactors
  let a : ℤ := -27*(e:ℤ)^2
  let X := (Z:ℚ)/(k:ℚ)^2
  let Y := ((c*v:ℕ):ℚ)/(k:ℚ)^3
  have an : a≠0 := mul_ne_zero (by decide) (pow_ne_zero _ (by exact_mod_cast ep.ne'))
  have aa : a.natAbs=27*e^2 := by simp [a,Int.natAbs_mul,Int.natAbs_pow]
  have ps : ∀ p ∈ S, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have asup : a.natAbs.primeFactors ⊆ S := by
    rw [aa,show (27:ℕ)=3^3 by decide,Nat.primeFactors_mul (by decide) (pow_ne_zero _ ep.ne'),
      Nat.primeFactors_pow 3 (by decide : 3≠0),Nat.primeFactors_pow e (by decide : 2≠0)]
    exact Finset.union_subset (Nat.primeFactors_mono (dvd_mul_right 3 w) (by positivity))
      (Nat.primeFactors_mono (ed.trans (dvd_mul_left w 3)) (by positivity))
  have scaled : Y^2 = X^3+(a:ℚ) := by
    have z : (Z:ℚ)^3=((c:ℚ)*v)^2+27*((k:ℚ)^3*e)^2 := by exact_mod_cast fac ▸ eqn
    dsimp [Y,X,a]
    push_cast
    field_simp [show (k:ℚ)≠0 by exact_mod_cast kp.ne']
    linear_combination -z
  have bh := published S a X Y ps an asup (scaled_sIntegral kw wp kp Z 2 (by decide))
    (scaled_sIntegral kw wp kp (c*v) 3 (by decide)) scaled
  let N := ∏ p ∈ S,p
  have Nrad : N=radical (3*w) := Nat.radical_eq_prod_primeFactors.symm
  have Npos : 0<N := Nrad ▸ Nat.radical_pos _
  have Nb : N≤90*D^11 := calc
    _ = radical (3*w) := Nrad
    _ ≤ radical 3*radical w := Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos _) (Nat.radical_pos _)) radical_mul_dvd
    _ ≤ 3*(30*D^11) := Nat.mul_le_mul (Nat.radical_le_self_iff.mpr (by decide)) small
    _ = _ := by ring
  have eb : e≤900*D^22 := calc
    _ ≤ (radical w)^2 := er
    _ ≤ (30*D^11)^2 := Nat.pow_le_pow_left small 2
    _ = _ := by ring
  have aBound : a.natAbs ≤ 10^8*D^44 := calc
    _ = 27*e^2 := aa
    _ ≤ 27*(900*D^22)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left eb 2)
    _ = 21870000*D^44 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  have bBound : 62208*N^2 ≤ 10^9*D^22 := calc
    _ ≤ 62208*(90*D^11)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Nb 2)
    _ = 503884800*D^22 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  have bOne : 1 ≤ 62208*N^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hX := real_envelope (D:=(D:ℝ)) (by exact_mod_cast d1)
    (by exact_mod_cast Int.natAbs_pos.mpr an : (0:ℝ)<a.natAbs)
    (by exact_mod_cast bOne : (1:ℝ)≤62208*(N:ℝ)^2)
    (by exact_mod_cast aBound) (by exact_mod_cast bBound) bh
  let V := max |(X.num:ℝ)| (X.den:ℝ)
  have vp : 0<V := lt_of_lt_of_le (by exact_mod_cast X.den_pos : (0:ℝ)<X.den) (le_max_right _ _)
  have loss := Real.log_le_log (by exact_mod_cast zp : (0:ℝ)<Z)
    (numerator_loss kp cw cp c27 kd eqn)
  change Real.log (Z:ℝ) ≤ Real.log (729*V) at loss
  rw [Real.log_mul (by norm_num) vp.ne'] at loss
  change Real.log V ≤ _ at hX
  have lc := Real.log_le_sub_one_of_pos (by norm_num : 0<(729:ℝ))
  have big : (1:ℝ)≤(D:ℝ)^24 := one_le_pow₀ (by exact_mod_cast d1)
  linarith

end
end ZInQBlueprint.TwistDescent
#print axioms ZInQBlueprint.TwistDescent.support_mordell_height
