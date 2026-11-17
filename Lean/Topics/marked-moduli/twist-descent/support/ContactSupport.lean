import SupportHeight

/-! A bound for the geometric six-contact twists outside one explicit prime-support condition. -/
open ZInQ ZInQBlueprint.OddSupport UniqueFactorizationMonoid
namespace ZInQBlueprint.TwistDescent
noncomputable section

/-- The two coprime primitive cubic coordinates, with their common cube norm. -/
theorem primitive_twist_coordinates {d : ℤ} {x y : ℚ} (hd : d≠0) (ny : y≠0)
    (point : 30*(d:ℚ)*y^2=quintic x) :
    ∃ k P Q T : ℤ, (k=1 ∨ k=2) ∧ P≠0 ∧ Q≠0 ∧ P.natAbs.Coprime Q.natAbs ∧
      0<T ∧ P^2+27*Q^2=T^3 ∧ k^2*T=quadraticNorm x.num x.den ∧
      k^3*P=realCubic x.num x.den ∧ k^3*Q=imaginaryCubic x.num x.den := by
  obtain ⟨k,P,Q,T,hk,p,q,t,cop,eqn⟩ := primitive_norm x.num (x.den:ℤ) (by simpa using x.reduced)
  have prod := product_at_twist point
  have hnt : (30:ℚ)*(d:ℚ)*(y*(x.den:ℚ)^3)^2≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hd))
      (pow_ne_zero _ (mul_ne_zero ny (pow_ne_zero _ (by exact_mod_cast x.den_ne_zero))))
  have both := prod ▸ hnt
  rw [←p,←q] at both
  have pn : P≠0 := by intro h; subst P; simp at both
  have qn : Q≠0 := by intro h; subst Q; simp at both
  exact ⟨k,P,Q,T,hk,pn,qn,cop,(norm_height x hk t).1,eqn,t,p,q⟩

/-- Either primitive coordinate can be chosen as the coefficient in the rescaled model. -/
theorem contact_support_height (published : SupportedMordell74)
    {k P Q T : ℤ} {D : ℕ} {x : ℚ} (d1 : 1≤D) (hk : k=1 ∨ k=2)
    (pn : P≠0) (qn : Q≠0) (cop : P.natAbs.Coprime Q.natAbs)
    (eqn : P^2+27*Q^2=T^3) (norm : k^2*T=quadraticNorm x.num x.den)
    (small : min (radical P.natAbs) (radical Q.natAbs) ≤ 30*D^11) :
    ratHeight x ≤ 10^30*(D:ℝ)^24 := by
  obtain ⟨tp,_,hx⟩ := norm_height x hk norm
  have natEq : P.natAbs^2+27*Q.natAbs^2=T.natAbs^3 := by
    zify
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs,
      sq_abs,abs_of_pos tp] using eqn
  have hT : 0<T.natAbs := Int.natAbs_pos.mpr tp.ne'
  have h : Real.log (T.natAbs:ℝ)≤10^30*(D:ℝ)^24 := by
    rcases min_le_iff.mp small with sm|sm
    · have e : (3*T.natAbs)^3 = (27*Q.natAbs)^2+27*P.natAbs^2 := by nlinarith only [natEq]
      have l := support_mordell_height published d1 (Nat.mul_pos (by decide) hT)
        (Int.natAbs_pos.mpr pn) cop (by decide : 0<27) (by decide) e sm
      apply le_trans _ l
      apply Real.log_le_log (by exact_mod_cast hT)
      exact_mod_cast (show T.natAbs≤3*T.natAbs by omega)
    · have e : T.natAbs^3=(1*P.natAbs)^2+27*Q.natAbs^2 := by simpa using natEq.symm
      exact support_mordell_height published d1 hT (Int.natAbs_pos.mpr qn) cop.symm
        (by decide : 0<1) (by decide) e sm
  have tr : (T.natAbs:ℝ)=(T:ℝ) := by rw [Nat.cast_natAbs,Int.cast_abs,abs_of_pos (by exact_mod_cast tp)]
  rw [tr] at h
  have one : (1:ℝ)≤(D:ℝ)^24 := one_le_pow₀ (by exact_mod_cast d1)
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

/-- The old size condition on the two square multipliers implies the new prime support
condition. For this implication the size of each multiplier can already be replaced
by the product of its distinct prime divisors. -/
theorem multiplier_support {D : ℕ} {r s m n : ℤ}
    (r0 : r≠0) (s0 : s≠0) (bound : r.natAbs*s.natAbs ≤ 30*D)
    (small : min (radical m.natAbs) (radical n.natAbs) ≤ D^10) :
    min (radical (r*m^2).natAbs) (radical (s*n^2).natAbs) ≤ 30*D^11 := by
  have side (u l : ℤ) (un : u≠0) (ub : u.natAbs ≤ 30*D)
      (lb : radical l.natAbs ≤ D^10) : radical (u*l^2).natAbs ≤ 30*D^11 := by
    rw [Int.natAbs_mul,Int.natAbs_pow]
    calc
      _ ≤ radical u.natAbs * radical (l.natAbs^2) :=
        Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos _) (Nat.radical_pos _)) radical_mul_dvd
      _ = radical u.natAbs * radical l.natAbs := by rw [radical_pow _ (by decide)]
      _ ≤ (30*D)*D^10 := Nat.mul_le_mul
        ((Nat.radical_le_self_iff.mpr (Int.natAbs_ne_zero.mpr un)).trans ub) lb
      _ = _ := by ring
  have rb : r.natAbs ≤ r.natAbs*s.natAbs := by
    simpa only [mul_one] using Nat.mul_le_mul_left r.natAbs (show 1 ≤ s.natAbs from Int.natAbs_pos.mpr s0)
  have sb : s.natAbs ≤ r.natAbs*s.natAbs := by
    simpa only [one_mul] using Nat.mul_le_mul_right s.natAbs (show 1 ≤ r.natAbs from Int.natAbs_pos.mpr r0)
  rcases min_le_iff.mp small with h|h
  · exact min_le_iff.mpr (Or.inl (side r m r0 (rb.trans bound) h))
  · exact min_le_iff.mpr (Or.inr (side s n s0 (sb.trans bound) h))

/-- Only geometric tuples with both large prime supports are required in the remaining case. -/
def LargeContactSupport (H : ℝ) : Prop :=
  ∀ (d : ℤ) (x y : ℚ) (k P Q : ℤ), Squarefree d → y≠0 → x≠5 →
    30*(d:ℚ)*y^2=quintic x → (k=1 ∨ k=2) → P.natAbs.Coprime Q.natAbs →
    k^3*P=realCubic x.num x.den → k^3*Q=imaginaryCubic x.num x.den →
    30*d.natAbs^11 < min (radical P.natAbs) (radical Q.natAbs) → ratHeight x≤H*(d.natAbs:ℝ)^24

theorem sixContact_of_large_support (published : SupportedMordell74)
    (remaining : LargeContactSupport publicTwistConstant) : SixContactMin := by
  apply sixContactMin_of_twistBound
  intro d x y sf ny exc point
  obtain ⟨k,P,Q,T,hk,pn,qn,cop,_,eqn,norm,p,q⟩ := primitive_twist_coordinates sf.ne_zero ny point
  by_cases sm : min (radical P.natAbs) (radical Q.natAbs) ≤ 30*d.natAbs^11
  · have h := contact_support_height published (Int.natAbs_pos.mpr sf.ne_zero) hk pn qn cop eqn norm sm
    have c : (10:ℝ)^30 ≤ publicTwistConstant := (by norm_num : (10:ℝ)^30≤10^60).trans public_margin
    exact h.trans (mul_le_mul_of_nonneg_right c (by positivity))
  · exact remaining d x y k P Q sf ny exc point hk cop p q (lt_of_not_ge sm)

end
end ZInQBlueprint.TwistDescent
#print axioms ZInQBlueprint.TwistDescent.primitive_twist_coordinates
#print axioms ZInQBlueprint.TwistDescent.contact_support_height
#print axioms ZInQBlueprint.TwistDescent.sixContact_of_large_support

#print axioms ZInQBlueprint.TwistDescent.multiplier_support
