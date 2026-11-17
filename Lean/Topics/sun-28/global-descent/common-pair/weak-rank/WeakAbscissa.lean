import ExcludedCompanionRank

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.MarkedDescent Sun28.CompanionRank Sun28.GlobalSections
open ZInQ.Descent ZInQ.RouteK WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

private theorem negative_class {u v : ℚ} (up : 0<u) (vn : v<0) : sqc u ≠ sqc v := by
  intro e
  obtain ⟨r,_,h⟩ := (sqc_eq_sqc_iff up.ne' vn.ne).mp e
  exact (not_lt_of_ge (h ▸ mul_nonpos_of_nonpos_of_nonneg vn.le (sq_nonneg r))) up

private theorem squarefree_eq {a b : ℕ} (sa : Squarefree a) (sb : Squarefree b)
    (h : sqc (a:ℚ)=sqc (b:ℚ)) : a=b := by
  obtain ⟨v,vn,hv⟩ := (sqc_eq_sqc_iff (by exact_mod_cast sa.ne_zero) (by exact_mod_cast sb.ne_zero)).mp h
  have e := sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sa) (t:=(1:ℚ)) one_ne_zero
    (by push_cast;ring : (a:ℚ)=(a:ℤ)*1^2)
  have f := sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sb) vn
    (by simpa only [Int.cast_natCast] using hv)
  exact_mod_cast e.symm.trans f

private theorem quotient_abscissa {l : ℕ} (lp : 0<l) {P T : RationalPoint l}
    (e : (QuotientAddGroup.mk P : ModTwo l)=QuotientAddGroup.mk T) :
    rootClass l 0 P=rootClass l 0 T := by
  obtain ⟨V,h⟩ := QuotientAddGroup.eq_iff_sub_mem.mp e
  have lp' : (0:ℚ)<l := by exact_mod_cast lp
  have root : (0:ℚ)*(0-l)*(0+3*l)=0 := by ring
  have dn : derivativeAt l 0≠0 := by unfold derivativeAt;nlinarith [sq_pos_of_pos lp']
  have point : P=T+(V+V) := by
    change (2:ℕ) • V=P-T at h
    rw [two_smul] at h
    rw [h]; abel
  rw [point,class_add root dn,class_add root dn,SqClass.mul_self,mul_one]

/-- The four evaluations are respectively 1, -3, l, -3l up to squares. -/
theorem abscissa_torsion {l : ℕ} (lp : 0<l) {T : RationalPoint l} (two : (2:ℕ) • T=0) :
    rootClass l 0 T=1 ∨ rootClass l 0 T=sqc (-3:ℚ) ∨
    rootClass l 0 T=sqc (l:ℚ) ∨ rootClass l 0 T=sqc (-3*(l:ℚ)) := by
  have nz : (l:ℚ)≠0 := by exact_mod_cast lp.ne'
  cases T with
  | zero => exact Or.inl rfl
  | @some x y S =>
    rw [ZInQ.two_nsmul_some_eq_zero_iff,neg_y] at two
    obtain rfl : y=0 := by linarith
    have eq := equation.mp S.1
    have v : x*(x-l)*(x+3*l)=0 := by simpa only [zero_pow (by decide : 2≠0)] using eq.symm
    rcases mul_eq_zero.mp v with h|h
    · rcases mul_eq_zero.mp h with hx|hl
      · subst x
        right;left
        simpa only [at_affine,ite_true,derivativeAt,zero_pow (by decide : 2≠0),mul_zero,zero_add,
          zero_sub,neg_mul] using sqc_mul_sq (-3:ℚ) nz
      · obtain rfl := sub_eq_zero.mp hl
        right;right;left
        simp only [at_affine,ite_eq_right nz,sub_zero]
    · have hx : x= -3*(l:ℚ) := by linarith
      subst x
      right;right;right
      simp only [at_affine,ite_eq_right (mul_ne_zero (by norm_num : (-3:ℚ)≠0) nz),sub_zero]

/-- A point having the positive proper squarefree abscissa class b lies
outside all rational torsion classes modulo doubles, for any second label. -/
theorem outside_torsion {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) {P : RationalPoint l} (mark : rootClass l 0 P=sqc (b:ℚ))
    {T : RationalPoint l} (two : (2:ℕ) • T=0) :
    (QuotientAddGroup.mk P : ModTwo l) ≠ QuotientAddGroup.mk T := by
  intro same
  have bp : 0<b := by omega
  have bl : b<l := by rw [fac];nlinarith
  have lp : 0<l := by omega
  have sb := (Nat.squarefree_mul_iff.mp (fac ▸ sf)).2.1
  have bpos : (0:ℚ)<b := by exact_mod_cast bp
  have lpos : (0:ℚ)<l := by exact_mod_cast lp
  have h := mark.symm.trans (quotient_abscissa lp same)
  rcases abscissa_torsion lp two with h1|h2|h3|h4
  · have one : sqc (b:ℚ)=sqc ((1:ℕ):ℚ) := by simpa only [Nat.cast_one,sqc_one] using h.trans h1
    exact (by omega : b≠1) (squarefree_eq sb squarefree_one one)
  · exact negative_class bpos (by norm_num) (h.trans h2)
  · exact bl.ne (squarefree_eq sb sf (h.trans h3))
  · exact negative_class bpos (by linarith) (h.trans h4)

/-- The individual affine weak point, with its given ordinate, has infinite order. -/
theorem affine_infinite {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) {u y : ℚ} (un : u≠0)
    (ns : (twistCurve l).toAffine.Nonsingular ((b:ℚ)*u^2) y) :
    ¬IsOfFinAddOrder (Point.some ((b:ℚ)*u^2) y ns) := by
  have bl : b<l := by rw [fac];nlinarith
  intro finite
  obtain ⟨T,two,same⟩ := torsion_representative (by omega : 1<l) sf finite
  apply outside_torsion bb kb fac sf (T:=T) (P:=Point.some ((b:ℚ)*u^2) y ns) _ two same
  have bp : (b:ℚ)≠0 := by exact_mod_cast (by omega : b≠0)
  simp only [at_affine,ite_eq_right (mul_ne_zero bp (pow_ne_zero _ un)),sub_zero,sqc_mul_sq _ un]

theorem strict_point_rank {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) (hit : strictPoint b l) :
    ∃ P : RationalPoint l, rootClass l 0 P=sqc (b:ℚ) ∧ ¬IsOfFinAddOrder P := by
  obtain ⟨u,y,un,yn,eq⟩ := hit
  have ns : (twistCurve l).toAffine.Nonsingular ((b:ℚ)*u^2) y := by
    rw [nonsingular_iff]
    refine ⟨equation.mpr eq, Or.inr ?_⟩
    simp only [twistCurve, WeierstrassCurve.toAffine,zero_mul,sub_zero]
    exact fun h => yn (by linarith)
  have bp : (b:ℚ)≠0 := by exact_mod_cast (by omega : b≠0)
  refine ⟨.some ((b:ℚ)*u^2) y ns,?_,affine_infinite bb kb fac sf un ns⟩
  simp only [at_affine,ite_eq_right (mul_ne_zero bp (pow_ne_zero _ un)),sub_zero,sqc_mul_sq _ un]

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.abscissa_torsion
#print axioms Sun28.WeakRank.outside_torsion
#print axioms Sun28.WeakRank.affine_infinite
#print axioms Sun28.WeakRank.strict_point_rank
