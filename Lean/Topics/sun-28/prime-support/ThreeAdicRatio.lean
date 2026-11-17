import LocalRatioResidual

namespace Sun28.PointLifts
open Sun28.PairedClasses
noncomputable section

private theorem unit_order {c : ℤ} (h : (c : ZMod 3) ≠ 0) : padicValRat 3 (c:ℚ) = 0 :=
  order_zero_of_residue (residue_int c) h

/-- On the conic with b congruent to two modulo three the abscissa
has order zero or one, including both zero-ordinate points. -/
theorem conic_three_orders {b : ℕ} {z h : ℚ} (bp : 0<b) (b3 : (b:ZMod 3)=2)
    (E : (z-1)*(z+3)=(b:ℚ)*h^2) : padicValRat 3 z = 0 ∨ padicValRat 3 z = 1 := by
  obtain ⟨x,y,prim,rfl⟩ := integral_abscissa bp E
  let D : ℤ := x^2-b*y^2
  let H : ℤ := x^2+3*b*y^2
  have primitive := primitive_mod (p:=3) prim
  have anis : ∀ i j : ZMod 3, (i≠0 ∨ j≠0) → i^2-2*j^2≠0 := by decide
  have du : (D:ZMod 3)≠0 := by simpa [D,b3] using anis _ _ primitive
  have dr : (D:ℚ)≠0 := by
    intro zero
    have zd : D=0 := by exact_mod_cast zero
    simp [zd] at du
  have form : abscissa b x y = (H:ℚ)/D := by simp [abscissa,D,H]
  rw [form]
  by_cases xp : (x:ZMod 3)=0
  · right
    have yp := primitive.resolve_left (not_not_intro xp)
    obtain ⟨u,hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp xp
    let C : ℤ := 3*u^2+b*y^2
    have cu : (C:ZMod 3)≠0 := by
      simp [C,b3,show (3:ZMod 3)=0 by decide,yp,show (2:ZMod 3)≠0 by decide]
    have cr : (C:ℚ)≠0 := by
      intro zero
      have zc : C=0 := by exact_mod_cast zero
      simp [zc] at cu
    have Hc : H=3*C := by dsimp [H,C];rw [hx];ring
    rw [Hc,Int.cast_mul,Int.cast_ofNat,padicValRat.div (mul_ne_zero (by norm_num) cr) dr,
      padicValRat.mul (by norm_num) cr,unit_order cu,unit_order du]
    simpa using padicValRat.self (p:=3) (by decide)
  · left
    have hu : (H:ZMod 3)≠0 := by simpa [H,show (3:ZMod 3)=0 by decide] using pow_ne_zero 2 xp
    have hr : (H:ℚ)≠0 := by
      intro zero
      have zh : H=0 := by exact_mod_cast zero
      simp [zh] at hu
    rw [padicValRat.div hr dr,unit_order hu,unit_order du,sub_zero]

theorem ratio_three_unit {b θ : ℕ} {s z h j : ℚ} (a : AdmissiblePair b θ)
    (F : ConicFibre b θ s z h j) : padicValRat 3 s=0 := by
  obtain ⟨bp,tp,_,_,_,_,_,bt,tt,_⟩ := a
  have B : (b:ZMod 3)=2 := by
    exact (ZMod.natCast_eq_natCast_iff b 2 3).mpr (show b ≡ 17 [MOD 3] from (show b ≡ 17 [MOD 24] from bt).of_dvd (by decide))
  have T : (θ:ZMod 3)≠0 := by
    have : (θ:ZMod 3)=(1:ℕ) := (ZMod.natCast_eq_natCast_iff θ 1 3).mpr ((show θ ≡ 1 [MOD 24] from tt).of_dvd (by decide))
    simp [this]
  have tn : (θ:ℚ)≠0 := by exact_mod_cast tp.ne'
  have tv : padicValRat 3 (θ:ℚ)=0 := by simpa using unit_order (c:=(θ:ℤ)) (by simpa using T)
  have first := conic_three_orders bp B F.first
  have second := conic_three_orders bp B F.second
  rw [padicValRat.mul (div_ne_zero (pow_ne_zero _ F.s_ne) tn) F.z_ne,
    padicValRat.div (pow_ne_zero _ F.s_ne) tn,padicValRat.pow,tv] at second
  omega

theorem three_unit_of_fibre {b θ : ℕ} (a : AdmissiblePair b θ)
    {s : ℚ} (sn : s≠0) (H : SingleFibre b θ s) : padicValRat 3 s=0 := by
  obtain ⟨z,h,j,F⟩ := (conics_iff_single (by exact_mod_cast a.1)
    (by exact_mod_cast a.2.1.ne') sn).mpr H
  exact ratio_three_unit a F

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.conic_three_orders
#print axioms Sun28.PointLifts.ratio_three_unit
#print axioms Sun28.PointLifts.three_unit_of_fibre
