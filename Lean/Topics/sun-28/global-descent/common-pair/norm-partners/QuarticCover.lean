import PartnerProjection

namespace Sun28.NormPartners
open Sun28.SelmerRealization Sun28.PairedClasses
noncomputable section

private theorem nonsquare_nat {m : ℕ} (sf : Squarefree m) (big : 1 < m) : ¬IsSquare (m:ℚ) := by
  rintro imp
  obtain ⟨z,e⟩ := Rat.isSquare_natCast_iff.mp imp
  rw [e] at sf big
  have hz := sf z dvd_rfl
  rw [Nat.isUnit_iff] at hz
  simp [hz] at big

private theorem exchange_criterion {b s : ℕ} (bb : 1<b) (ss : 1<s) :
    Cover ℚ (b*s) b 1 ↔ Cover ℚ (b*s) s 1 :=
  Sun28.LocalOrbit.exchange_iff (by exact_mod_cast (rfl : b*s=b*s)) (by positivity)

/-- On the complementary marked chart s(X²-b)=Y², Z²-X²=3b.
The line coordinate t=X+Z turns the latter equation into a factorization. -/
theorem family_of_cover {b s : ℕ} (bb : 1<b) (ss : 1<s) (sf : Squarefree (b*s))
    (pt : Cover ℚ (b*s) b 1) : Family b s := by
  have sb := (Nat.squarefree_mul_iff.mp sf).2.1
  have sq := (Nat.squarefree_mul_iff.mp sf).2.2
  have bp : 0<(b:ℚ) := by exact_mod_cast (show 0<b by omega)
  have sp : 0<(s:ℚ) := by exact_mod_cast (show 0<s by omega)
  have H := (rational_cover (b*s) s).mp ((exchange_criterion bb ss).mp pt)
  have non : ¬IsSquare ((b:ℚ)*s/s) := by
    rw [mul_div_cancel_right₀ _ sp.ne']
    exact nonsquare_nat sb bb
  obtain ⟨U,V,W,_,vn,_,one,two⟩ := Sun28.SupportMatrix.cover_affine
    sp (mul_pos bp sp) (nonsquare_nat sq ss) non (by simpa only [Int.cast_natCast,Nat.cast_mul] using H)
  have rel : W^2-U^2=3*(b:ℚ) := by
    apply mul_left_cancel₀ sp.ne'
    linear_combination -two
  let t := U+W
  have prod : t*(W-U)=3*b := by dsimp [t]; nlinarith only [rel]
  have tn : t≠0 := by intro zero;rw [zero,zero_mul] at prod; linarith
  have ft : t^2-3*b=2*t*U := by dsimp [t]; nlinarith only [rel]
  have square : (t^2-b)*(t^2-9*b)=4*t^2*(U^2-b) := by
    calc (t^2-b)*(t^2-9*b) = (t^2-3*b)^2-4*b*t^2 := by ring
         _ = 4*t^2*(U^2-b) := by rw [ft];ring
  refine ⟨t/3,2*t*V/(3*s),div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) tn) vn) (mul_ne_zero (by norm_num) sp.ne'),?_⟩
  calc
    _ = (t^2-b)*(t^2-9*b)/9 := by ring
    _ = (4*t^2/9)*(U^2-b) := by rw [square];ring
    _ = (4*t^2/9)*(V^2/s) := by
      congr 1
      apply (eq_div_iff sp.ne').mpr
      linear_combination one
    _ = _ := by field_simp [sp.ne'];ring

/-- Conversely a point of the old quartic family gives a rational point
on the prescribed (b,1) cover. Parameters may have either sign. -/
theorem cover_of_family {b s : ℕ} (bb : 1<b) (ss : 1<s) (sf : Squarefree (b*s))
    (H : Family b s) : Cover ℚ (b*s) b 1 := by
  obtain ⟨k,h,hn,F⟩ := H
  have bp : 0<(b:ℚ) := by exact_mod_cast (show 0<b by omega)
  have sp : 0<(s:ℚ) := by exact_mod_cast (show 0<s by omega)
  have kn : k≠0 := by
    rintro rfl
    apply nonsquare_nat (Nat.squarefree_mul_iff.mp sf).2.2 ss
    refine ⟨(b:ℚ)/h,?_⟩
    field_simp
    linear_combination -F
  apply (exchange_criterion bb ss).mpr
  let U := (3*k^2-b)/(2*k)
  let V := (s:ℚ)*h/(2*k)
  let W := (3*k^2+b)/(2*k)
  refine ⟨U,V,W,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩
  · push_cast;dsimp [U,V];field_simp [kn];linear_combination F
  · push_cast;dsimp [U,W];field_simp [kn];ring

theorem cover_iff_family {b s : ℕ} (bb : 1<b) (ss : 1<s) (sf : Squarefree (b*s)) :
    Cover ℚ (b*s) b 1 ↔ Family b s :=
  ⟨family_of_cover bb ss sf,cover_of_family bb ss sf⟩

end
end Sun28.NormPartners

#print axioms Sun28.NormPartners.family_of_cover
#print axioms Sun28.NormPartners.cover_of_family
#print axioms Sun28.NormPartners.cover_iff_family
