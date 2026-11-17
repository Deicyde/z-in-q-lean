import SignedSections

namespace Sun28.SupportMatrix
open Sun28.PrescribedPoints

/-- Homogeneous equations for the marked 2-cover in the coordinates
(x+3l,x-l). A nonzero tuple represents its projective class. -/
def MarkedCover (b l : ℚ) : Prop := ∃ X Y Z T : ℚ,
  (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0 ∨ T ≠ 0) ∧
  b*X^2-Y^2=l*T^2 ∧ b*(Z^2-X^2)=3*l*T^2

/-- Positivity and two squareclass checks remove every exceptional chart. -/
theorem cover_affine {b l : ℚ} (bp : 0<b) (lp : 0<l)
    (bs : ¬IsSquare b) (ls : ¬IsSquare (l/b)) (H : MarkedCover b l) :
    ∃ u v w : ℚ, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
      b*u^2-l=v^2 ∧ b*u^2+3*l=b*w^2 := by
  obtain ⟨X,Y,Z,T,proj,h1,h2⟩ := H
  have Tn : T≠0 := by
    intro ht
    subst T
    simp only [zero_pow (by decide : 2≠0), mul_zero] at h1 h2
    have Xn : X≠0 := by
      intro hx
      subst X
      have hy : Y=0 := by nlinarith
      have hz : Z=0 := by rcases mul_eq_zero.mp h2 with z|z <;> nlinarith
      simp [hy,hz] at proj
    apply bs
    refine ⟨Y/X, ?_⟩
    field_simp
    linarith
  have Xn : X≠0 := by
    intro hx
    subst X
    have pos := mul_pos lp (sq_pos_of_ne_zero Tn)
    nlinarith [sq_nonneg Y]
  have Yn : Y≠0 := by
    intro hy
    subst Y
    apply ls
    refine ⟨X/T, ?_⟩
    field_simp
    linarith
  have Zn : Z≠0 := by
    intro hz
    subst Z
    have pos := mul_pos lp (sq_pos_of_ne_zero Tn)
    have nn := mul_nonneg bp.le (sq_nonneg X)
    nlinarith
  refine ⟨X/T,Y/T,Z/T, div_ne_zero Xn Tn, div_ne_zero Yn Tn, div_ne_zero Zn Tn, ?_, ?_⟩
  · field_simp; linarith
  · field_simp; linarith

theorem pair_of_covers {b l θ : ℚ} (bp : 0<b) (lp : 0<l) (tp : 0<θ)
    (bs : ¬IsSquare b) (ls : ¬IsSquare (l/b)) (lθs : ¬IsSquare (l*θ/b))
    (first : MarkedCover b l) (second : MarkedCover b (l*θ)) : NonzeroPair b θ := by
  obtain ⟨u,v,w,un,vn,wn,one,two⟩ := cover_affine bp lp bs ls first
  obtain ⟨U,V,W,Un,Vn,Wn,One,Two⟩ := cover_affine bp (mul_pos lp tp) bs lθs second
  refine ⟨l,u,U,b*u*v*w,b*U*V*W,lp.ne',un,Un,by positivity,by positivity,?_,?_⟩
  · rw [one,two]; ring
  · rw [One,Two]; ring

theorem prepared_if_covers (first : MarkedCover 526361 174225491)
    (second : MarkedCover 526361 91761255825371) : NonzeroPair 526361 526681 := by
  apply pair_of_covers (l:=174225491) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) first
  simpa only [show (174225491:ℚ)*526681=91761255825371 by norm_num] using second

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.cover_affine
#print axioms Sun28.SupportMatrix.pair_of_covers
#print axioms Sun28.SupportMatrix.prepared_if_covers
