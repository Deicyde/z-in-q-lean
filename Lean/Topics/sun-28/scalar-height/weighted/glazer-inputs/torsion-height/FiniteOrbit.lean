import HeightGrowth

namespace ZInQBlueprint.MarkedTorsion
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open ZInQBlueprint.OriginalConcentrated ZInQBlueprint.OriginalHeightCount
open Height Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open scoped Classical
noncomputable section
set_option exponentiation.threshold 1024
attribute [local irreducible] glazerConstant24

def primitivePair {j:Fin 5} {d:ℚ} (P:(model j d).toAffine.Point) : ℤ×ℤ :=
  match P with
  | .zero => (1,0)
  | .some x _ _ => ((x/d).num,(x/d).den)

def pointBox {j:Fin 5} {d:ℚ} (P:(model j d).toAffine.Point) : ℤ :=
    box (primitivePair P).1 (primitivePair P).2

theorem pair_represents {j:Fin 5} {d:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point) :
    Represents P ((primitivePair P).1:ℚ) ((primitivePair P).2:ℚ) ∧
      IsCoprime (primitivePair P).1 (primitivePair P).2 ∧ 0<pointBox P := by
  cases P with
  | zero => simp [Represents,primitivePair,pointBox,box,isCoprime_one_left]
  | some x y valid =>
    let t:=x/d
    have nt : (t.num:ℚ)=t*t.den := by have eq:=t.num_div_den;field_simp at eq;simpa only [mul_comm t] using eq
    have xt : x=d*t := by dsimp [t];field_simp
    refine ⟨?_,t.isCoprime_num_den,?_⟩
    · change d*(t.num:ℚ)=x*((t.den:ℤ):ℚ)
      rw [nt,Int.cast_natCast,xt];ring
    · change 0 < max |t.num| |(t.den:ℤ)|
      exact (abs_pos.mpr (by exact_mod_cast t.den_ne_zero)).trans_le (le_max_right ..)

theorem duplication_growth {j:Fin 5} {d:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point) :
    (pointBox P)^4 ≤ 2^180*pointBox (P+P) := by
  let u:=(primitivePair P).1
  let v:=(primitivePair P).2
  let n:=(primitivePair (P+P)).1
  let e:=(primitivePair (P+P)).2
  obtain ⟨p,prim,hp⟩:=pair_represents dn P
  obtain ⟨q,pr, _⟩:=pair_represents dn (P+P)
  have eq:=cross dn (P+P) (represents_double dn P p) q
  have integral : N (a j) (b j) (c j) u v*e = D (a j) (b j) (c j) u v*n := by
    apply Int.cast_injective (α:=ℚ)
    push_cast [N,D,F]
    exact eq
  obtain ⟨g,g1,g2⟩:=primitive_proportional pr integral
  exact primitive_growth j prim g1 g2 hp

theorem finite_box {j:Fin 5} {d:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point)
    (tor:IsOfFinAddOrder P) : pointBox P≤2^60 := by
  obtain ⟨m,mp,stop⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp tor
  let f:ℕ→ℤ:=fun n=>pointBox (n • P)
  obtain ⟨n,_,big⟩:=Finset.exists_max_image (Finset.range m) f (Finset.nonempty_range_iff.mpr (by omega))
  have upper (z:ℕ) : f z≤f n := by
    have e:=nsmul_eq_mod_nsmul (a:=P) z stop
    change pointBox (z • P)≤_
    rw [e];exact big _ (Finset.mem_range.mpr (Nat.mod_lt _ mp))
  have dbl:=duplication_growth dn (n • P)
  have ud:=upper (2*n)
  change pointBox ((2*n) • P)≤f n at ud
  rw [mul_nsmul,two_nsmul,nsmul_add] at ud
  have he:(f n)^4 ≤ 2^180*f n := dbl.trans (mul_le_mul_of_nonneg_left ud (by positivity))
  have pn:0<f n:=(pair_represents dn (n • P)).2.2
  have joined : (f n)^3 ≤ (2:ℤ)^180 := by
    rw [pow_succ] at he
    exact (mul_le_mul_iff_left₀ pn).mp he
  have cap:f n≤2^60 := by
    by_contra! z
    have z3:=pow_lt_pow_left₀ z (by positivity:(0:ℤ)≤2^60) (by decide : 3≠0)
    rw [←pow_mul] at z3
    exact (not_lt_of_ge joined) z3
  have u:=upper 1
  simpa [f] using u.trans cap

private theorem height_of_rep {j:Fin 5} {d t:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point)
    (h:Represents P t 1) (tor:IsOfFinAddOrder P) : logHeight₁ t≤60 := by
  have boxh:=finite_box dn P tor
  cases P with
  | zero => change (1:ℚ)=0 at h;norm_num at h
  | some x y valid =>
    change d*t=x*1 at h
    have eq : x/d=t:=by field_simp;linear_combination -h
    change max |(x/d).num| |((x/d).den:ℤ)|≤2^60 at boxh
    rw [eq] at boxh
    have bnd:max t.num.natAbs t.den≤2^60 := by
      exact_mod_cast (by simpa only [←Int.natCast_natAbs,Int.natAbs_natCast] using boxh :
        max (t.num.natAbs:ℤ) (t.den:ℤ)≤2^60)
    rw [Rat.logHeight₁_eq_log_max]
    have real:=Real.log_le_log (by exact_mod_cast t.den_pos.trans_le (le_max_right t.num.natAbs t.den) :
      0<((max t.num.natAbs t.den:ℕ):ℝ)) (by exact_mod_cast bnd :
      ((max t.num.natAbs t.den:ℕ):ℝ)≤(2:ℝ)^60)
    rw [Real.log_pow] at real;norm_num only [Nat.cast_ofNat] at real
    linarith [Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

theorem torsion_height {j:Fin 5} {d s:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point)
    (rep:Represents P ((k j:ℚ)*chart j s) 1) (tor:IsOfFinAddOrder P) : logHeight₁ s≤80 := by
  have h:=height_of_rep dn P rep tor
  have result:=logHeight₁_mul_le ((k j:ℚ)*chart j s) ((k j:ℚ)⁻¹)
  rw [mul_right_comm,mul_inv_cancel₀ (by fin_cases j <;> decide : (k j:ℚ)≠0),one_mul,
    logHeight₁_inv] at result
  have th:logHeight₁ (chart j s)=logHeight₁ s := by
    unfold chart;split
    · exact logHeight₁_inv _
    · rfl
  have hk:logHeight₁ (k j:ℚ)≤20 := by
    rw [Rat.logHeight₁_eq_log_max]
    have bound : max (k j:ℚ).num.natAbs (k j:ℚ).den≤2^20 := by fin_cases j <;> decide
    have ll:=Real.log_le_log (by exact_mod_cast (k j:ℚ).den_pos.trans_le (le_max_right ..) :
      0<((max (k j:ℚ).num.natAbs (k j:ℚ).den:ℕ):ℝ)) (by exact_mod_cast bound :
      ((max (k j:ℚ).num.natAbs (k j:ℚ).den:ℕ):ℝ)≤(2:ℝ)^20)
    rw [Real.log_pow] at ll;norm_num only [Nat.cast_ofNat] at ll
    linarith [Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]
  linarith [th]

theorem infinite_orders_at_failure {s:ℚ} (bad:failure s) (j:Fin 5) :
    ∃ P:(model j (signedTwist j s:ℚ)).toAffine.Point,
      Represents P ((k j:ℚ)*chart j s) 1 ∧ ¬IsOfFinAddOrder P := by
  obtain ⟨P,h⟩:=represented_point bad.1 j
  have dn:(signedTwist j s:ℚ)≠0 := by
    obtain ⟨y,yn,v⟩:=point_on_twist bad.1 j
    intro z;rw [z,zero_mul] at v;exact (pow_ne_zero 2 yn) v
  refine ⟨P,h,fun tor=>?_⟩
  have hh:=torsion_height dn P h tor
  let T:=heightRadical s.num s.den
  have pos : (1:ℝ)≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd s.num s.den))
  have large:(80:ℝ)≤2^810:=(by norm_num:(80:ℝ)≤2^7).trans (pow_le_pow_right₀ (by norm_num) (by decide))
  have lower := large.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ pos (n:=24)))
  exact (not_lt_of_ge (hh.trans (lower.trans (original_margin s.num s.den)))) bad.2

end
end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.duplication_growth
#print axioms ZInQBlueprint.MarkedTorsion.finite_box
#print axioms ZInQBlueprint.MarkedTorsion.torsion_height
#print axioms ZInQBlueprint.MarkedTorsion.infinite_orders_at_failure
