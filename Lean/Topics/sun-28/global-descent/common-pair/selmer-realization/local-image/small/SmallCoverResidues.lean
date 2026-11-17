import PrimitiveCoverChart
import DyadicCoverTest
import SeededRealization

namespace Sun28.SmallImage
open Sun28.SelmerRealization
noncomputable section

/-- The real image has positive first Kummer coordinate. -/
theorem arch_first {l : ℕ} (lp : 0<l) {a b : ℤ} (ha : a≠0) (hb : b≠0)
    (h : Cover ℝ l a b) : 0<a := by
  obtain ⟨x,y,z,t,prim,e,f⟩:=h
  by_contra! notpos
  have neg : (a:ℝ)<0 := by exact_mod_cast lt_of_le_of_ne notpos ha
  have lp' : (0:ℝ)<l := by exact_mod_cast lp
  rcases lt_or_gt_of_ne hb with bn|bp
  · have : (b:ℝ)<0 := by exact_mod_cast bn
    have pos : 0<(a:ℝ)*b := mul_pos_of_neg_of_neg neg this
    have t0 : t=0 := by
      by_contra ht
      nlinarith [mul_nonpos_of_nonpos_of_nonneg neg.le (sq_nonneg z),mul_nonneg pos.le (sq_nonneg x),mul_pos lp' (sq_pos_of_ne_zero ht)]
    rw [t0] at e f
    have x0 : x=0 := by by_contra hx; nlinarith [mul_pos pos (sq_pos_of_ne_zero hx),mul_nonpos_of_nonpos_of_nonneg this.le (sq_nonneg y)]
    rw [x0] at e f
    have y0 : y=0 := by by_contra hy; nlinarith [mul_neg_of_neg_of_pos this (sq_pos_of_ne_zero hy)]
    have z0 : z=0 := by by_contra hz; nlinarith [mul_neg_of_neg_of_pos neg (sq_pos_of_ne_zero hz)]
    simp [x0,y0,z0,t0] at prim
  · have : (0:ℝ)<b := by exact_mod_cast bp
    have negab : (a:ℝ)*b<0 := mul_neg_of_neg_of_pos neg this
    have t0 : t=0 := by
      by_contra ht
      nlinarith [mul_pos lp' (sq_pos_of_ne_zero ht),mul_nonpos_of_nonpos_of_nonneg negab.le (sq_nonneg x),mul_nonneg this.le (sq_nonneg y)]
    rw [t0] at e f
    have x0 : x=0 := by by_contra hx; nlinarith [mul_neg_of_neg_of_pos negab (sq_pos_of_ne_zero hx),mul_nonneg this.le (sq_nonneg y)]
    rw [x0] at e f
    have y0 : y=0 := by by_contra hy; nlinarith [mul_pos this (sq_pos_of_ne_zero hy)]
    have z0 : z=0 := by by_contra hz; nlinarith [mul_neg_of_neg_of_pos neg (sq_pos_of_ne_zero hz)]
    simp [x0,y0,z0,t0] at prim

theorem dyadic_image {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (h : Cover ℚ_[2] n a b) : a%2=1 ∧ b%2=1 := by
  obtain ⟨x,y,z,t,prim,e,f⟩ := residue_cover 5 h
  change _=11*t^2 at e
  change _=1*t^2 at f
  have rm (i : ℤ) (hi : Squarefree i) : (i:ZMod 32).val%4≠0 := by
    have h4 : ¬(4:ℤ)∣i := fun d=>(by decide : ¬ IsUnit (2:ℤ)) (hi 2 d)
    have V := ZMod.val_intCast (n:=32) i
    norm_num only [Nat.cast_ofNat] at V
    omega
  obtain ⟨A,B⟩ := dyadic_table _ _ _ _ _ _ (rm a ha) (rm b hb) prim e f
  have va := ZMod.val_intCast (n:=32) a
  have vb := ZMod.val_intCast (n:=32) b
  norm_num only [Nat.cast_ofNat] at va vb
  omega

end
end Sun28.SmallImage
#print axioms Sun28.SmallImage.arch_first
#print axioms Sun28.SmallImage.dyadic_image
