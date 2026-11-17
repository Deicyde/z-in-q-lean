import SignedSurface

namespace Sun28.PointConstruction
open Sun28.TwistExtension Sun28.PairedClasses
noncomputable section

def mark : ℚ := 526361
def other : ℚ := 526681
def seed : ℚ := -9991336979

def SignedQuartic (b q:ℚ) := ∃ u v y:ℚ, y≠0 ∧ y^2=q*quartic b u v

theorem signed_mark_iff {b q:ℚ} (bp:0<b) (qn:q≠0) :
    Point b (b*q) ↔ SignedQuartic b q := by
  rw [point_quartic bp (mul_ne_zero bp.ne' qn)]
  constructor
  · rintro ⟨u,v,w,h⟩
    let F:=quartic b u v
    have e : q = F*w^2 := by
      apply mul_left_cancel₀ bp.ne'; simpa only [mul_assoc] using h
    have fn : F≠0 := by rintro zero;rw [e,zero,zero_mul] at qn;contradiction
    have wn : w≠0 := by rintro rfl;rw [e] at qn;simp at qn
    refine ⟨u,v,F*w,mul_ne_zero fn wn,?_⟩
    change (F*w)^2=q*F
    rw [e];ring
  · rintro ⟨u,v,y,yn,eq⟩
    refine ⟨u,v,q/y,?_⟩
    field_simp [yn]
    exact eq

theorem seeded_quartic : (5262247351436699:ℚ)^2 = seed*other*quartic mark 1478 9 := by
  norm_num [seed,other,mark,quartic]

/-- On the second elliptic curve the exact seed has a nonzero ordinate and abscissa. -/
theorem seeded_second_nonzero_ordinate :
    ∃ t y:ℚ, t≠0 ∧ y≠0 ∧
      y^2=(mark*t^2)*(mark*t^2-(mark*seed*other))*(mark*t^2+3*(mark*seed*other)) := by
  let w : ℚ := seed*other/5262247351436699
  let D : ℚ := 1478^2+3*mark*9^2
  use D*w,4*mark^2*1478*9*D^2*w^3
  norm_num [mark,seed,other,w,D]

/-- With the physical second point verified, the first marked curve is the sole
remaining requirement for this particular twist. -/
theorem seeded_pair_iff : (Point mark (mark*seed) ∧ Point mark ((mark*seed)*other)) ↔
    Point mark (mark*seed) := by
  obtain ⟨t,y,tn,_,ey⟩:=seeded_second_nonzero_ordinate
  exact ⟨And.left,fun h=>⟨h,t,y,tn,ey⟩⟩

theorem seeded_first_quartic_iff :
    (Point mark (mark*seed) ∧ Point mark ((mark*seed)*other)) ↔ SignedQuartic mark seed :=
  seeded_pair_iff.trans (signed_mark_iff (by norm_num [mark]) (by norm_num [seed]))

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.signed_mark_iff
#print axioms Sun28.PointConstruction.seeded_quartic
#print axioms Sun28.PointConstruction.seeded_second_nonzero_ordinate
#print axioms Sun28.PointConstruction.seeded_pair_iff
#print axioms Sun28.PointConstruction.seeded_first_quartic_iff
