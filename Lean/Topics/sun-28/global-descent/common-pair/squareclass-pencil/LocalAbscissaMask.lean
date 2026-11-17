import OddGlobal

namespace Sun28.Abscissa
open Sun28.SelmerRealization Sun28.MarkedOdd ZInQ.RouteK.Selmer
variable {p : ℕ} [Fact p.Prime]

private theorem odd_value {z : Qp p} (nz : z≠0) (v : ‖z‖=(p:ℝ)⁻¹) : ¬IsSquare z := by
  intro H
  apply padic_norm_ne_zpow_odd nz H (-1)
  rw [v]
  norm_num

private theorem cancel {K : Type*} [Field K] {t c : K} (tz : t≠0)
    (M : SqEq t (c*t)) : IsSquare c := by
  obtain ⟨r,rn,E⟩:=M
  refine ⟨r⁻¹,?_⟩
  field_simp
  apply mul_left_cancel₀ tz
  linear_combination -E

/-- Over an odd bad prime, the ordered mark (b,1) and a second point of
abscissa class b with ramified second coordinate force -3 to be a square. -/
theorem split_of_ramified {l m b : ℕ} {a : ℤ} (large : 3 < p)
    (sf : Squarefree l) (pl : p∣l) (pm : p∣m) (dm : m∣l) (bp : 0 < b)
    (model : Cover (Qp p) l b 1) (weak : Cover (Qp p) l a m)
    (product : SqEq ((a:Qp p)*m) b) : IsSquare (-3 : ZMod p) := by
  let D:Qp p := l
  have ln : D≠0 := Nat.cast_ne_zero.mpr sf.ne_zero
  have sfm : Squarefree m := sf.squarefree_of_dvd dm
  have mn : (m:Qp p)≠0 := Nat.cast_ne_zero.mpr sfm.ne_zero
  have L : ‖D‖=(p:ℝ)⁻¹ := padic_norm_natCast_of_squarefree pl sf
  have noM : ¬IsSquare (m:Qp p) := odd_value mn (padic_norm_natCast_of_squarefree pm sfm)
  have N : ¬IsSquare (-D) := odd_value (neg_ne_zero.mpr ln) (by rw [norm_neg,L])
  have n3 : ¬(p:ℤ)∣(-3:ℤ) := by
    intro h
    have z : p∣3 := by exact_mod_cast (show (p:ℤ)∣3 by simpa using h)
    have := Nat.le_of_dvd (by decide : 0<3) z
    omega
  have U : ‖(-3:Qp p)‖=1 := by exact_mod_cast padic_norm_intCast_eq_one (p:=p) n3
  have V : ¬IsSquare (-3*D) := odd_value (mul_ne_zero (by norm_num) ln) (by rw [norm_mul,U,L,one_mul])
  have b0 : (b:ℤ)≠0 := by exact_mod_cast bp.ne'
  have W:=bad_classes (p:=p) (by omega) (by omega) pl sf b0 one_ne_zero model
  have B : SqEq (b:Qp p) 1 ∨ SqEq (b:Qp p) D := by
    rcases W with H|H|H|H
    · exact Or.inl H.1
    · exact Or.inr H.1
    all_goals exact (N (H.2.isSquare_iff.mp (by simp))).elim
  have a0 : a≠0 := by
    intro z;rw [z] at product
    exact product.ne_zero (Nat.cast_ne_zero.mpr bp.ne') (by simp)
  have T:=bad_classes (p:=p) (by omega) (by omega) pl sf a0 (by exact_mod_cast sfm.ne_zero) weak
  have A : SqEq (b:Qp p) (-3*D) ∨ SqEq (b:Qp p) (-3) := by
    rcases T with H|H|H|H
    · exact (noM (H.2.isSquare_iff.mpr (by simp))).elim
    · exact (noM (H.2.isSquare_iff.mpr (by simp))).elim
    · left
      convert product.symm.trans (H.1.mul H.2) using 1
      dsimp [D]
      ring
    · right
      have eq : SqEq ((3*D)*(-D)) (-3) := ⟨D,ln,by ring⟩
      exact product.symm.trans ((H.1.mul H.2).trans eq)
  have S : IsSquare (-3:Qp p) := by
    rcases B with B|B <;> rcases A with A|A
    · exact (V ((B.symm.trans A).isSquare_iff.mp (by simp))).elim
    · exact (B.symm.trans A).isSquare_iff.mp (by simp)
    · exact cancel ln (B.symm.trans A)
    · exact (V (by simpa only [mul_comm] using (B.symm.trans A).isSquare_mul)).elim
  have unit : ‖((-3:ℤ):ℤ_[p])‖=1 := by rw [PadicInt.norm_def,PadicInt.coe_intCast];exact_mod_cast U
  have red:=isSquare_coe_iff_toZMod (p:=p) (by omega) unit
  rw [PadicInt.coe_intCast,map_intCast] at red
  exact_mod_cast red.mp (by exact_mod_cast S)


/-- The square root of -3 gives a nontrivial cube root of unity in the residue field. -/
theorem prime_one_mod_three (large : 3 < p) (sq : IsSquare (-3 : ZMod p)) : p%3=1 := by
  obtain ⟨r,R⟩:=sq
  have two : (2:ZMod p)≠0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have three : (3:ZMod p)≠0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    exact Nat.not_dvd_of_pos_of_lt (by decide) large
  let w:ZMod p := (r-1)/2
  have Q : w^2+w+1=0 := by dsimp [w];field_simp;linear_combination -R
  have w0 : w≠0 := by rintro e;simp [e] at Q
  have w1 : w≠1 := by intro e;apply three;rw [e] at Q;linear_combination Q
  have cube : w^3=1 := by linear_combination (w-1)*Q
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ord:=orderOf_eq_prime cube w1
  have base:=ZMod.orderOf_dvd_card_sub_one w0
  rw [ord] at base
  omega

end Sun28.Abscissa
#print axioms Sun28.Abscissa.split_of_ramified
#print axioms Sun28.Abscissa.prime_one_mod_three
