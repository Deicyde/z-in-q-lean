import RegularFibre

namespace Sun28.GlobalSections
open Sun28.PointLifts Sun28.PrescribedPoints
noncomputable section

def lead (r : ℚ) := (r-1)*(r+3)
def rightRoot (r : ℚ) := (3*r+1)*(r+3)
def leftRoot (r : ℚ) := 3*(r-1)^2

def equation (r x y : ℚ) : Prop :=
  y^2=x*(x+rightRoot r)*(x+leftRoot r)

/-- The unmarked cubic depends only on r.  The prescribed b enters solely in its x-squareclass. -/
def represented (b r : ℚ) : Prop :=
  ∃ t y : ℚ, t≠0 ∧ y≠0 ∧ equation r (b*lead r*t^2) y

/-- The integral Weierstrass equation is split.  Its cubic discriminant is
nonzero away from its indicated roots and collisions. -/
def curve (r : ℚ) : WeierstrassCurve ℚ :=
  ⟨0,rightRoot r+leftRoot r,0,rightRoot r*leftRoot r,0⟩

theorem curve_discriminant (r : ℚ) : (curve r).Δ =
    16*(rightRoot r)^2*(leftRoot r)^2*(16*r)^2 := by
  simp [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈,rightRoot,leftRoot]
  ring

private theorem formula {b θ s r k : ℚ} (eq : θ*r=s^2) :
    singlePolynomial b θ s k 1=θ^2*((r-1)*k^2+(3*r+1)*b)*((r+3)*k^2+3*(r-1)*b) := by
  unfold singlePolynomial
  rw [←eq]
  ring

theorem quotient_of_cover {b r k h : ℚ} (bk : b≠0) (A : lead r≠0) (kn : k≠0) (hn : h≠0)
    (pt : b*h^2=((r-1)*k^2+(3*r+1)*b)*((r+3)*k^2+3*(r-1)*b)) :
    represented b r := by
  refine ⟨k/b,lead r*k*h/b,div_ne_zero kn bk,div_ne_zero (mul_ne_zero (mul_ne_zero A kn) hn) bk,?_⟩
  unfold equation
  have X : b*lead r*(k/b)^2=lead r*k^2/b := by field_simp
  rw [X]
  have b1 : lead r*k^2/b+rightRoot r=(r+3)*((r-1)*k^2+(3*r+1)*b)/b := by
    field_simp; unfold lead rightRoot;ring
  have b2 : lead r*k^2/b+leftRoot r=(r-1)*((r+3)*k^2+3*(r-1)*b)/b := by
    field_simp;unfold lead leftRoot;ring
  rw [b1,b2]
  calc
    _ = ((lead r*k)^2 / b^3)*(b*h^2) := by field_simp
    _ = _ := by rw [pt];unfold lead;ring

theorem cover_of_quotient {b r : ℚ} (bk : b≠0) (A : lead r≠0) (pt : represented b r) :
    ∃ k h : ℚ, k≠0 ∧ h≠0 ∧
      b*h^2=((r-1)*k^2+(3*r+1)*b)*((r+3)*k^2+3*(r-1)*b) := by
  obtain ⟨t,y,tn,yn,F⟩:=pt
  refine ⟨b*t,y/(lead r*t),mul_ne_zero bk tn,div_ne_zero yn (mul_ne_zero A tn),?_⟩
  unfold equation at F
  have b1 : b*lead r*t^2+rightRoot r=(r+3)*((r-1)*b*t^2+(3*r+1)) := by
    unfold lead rightRoot;ring
  have b2 : b*lead r*t^2+leftRoot r=(r-1)*((r+3)*b*t^2+3*(r-1)) := by
    unfold lead leftRoot;ring
  rw [b1,b2] at F
  calc
    _ = b*y^2/(lead r*t)^2 := by ring
    _ = _ := by rw [F];field_simp;unfold lead;ring

/-- A fibre off the previously solved boundary is exactly a squareclass
on a single split elliptic curve, with rational maps in both directions. -/
theorem single_iff_represented {b θ s:ℚ} (bp:0<b) (tp:0<θ) (sp:0<s) (short:s^2<θ)
    (nonsquare : ¬IsSquare b) (out:¬OneQuartic b θ) :
    SingleFibre b θ s ↔ represented b (s^2/θ) := by
  let r := s^2/θ
  have eq : θ*r=s^2 := by dsimp [r];field_simp
  have rp : 0<r := div_pos (sq_pos_of_pos sp) tp
  have rs : r<1 := (div_lt_one tp).mpr short
  have A : lead r≠0 := mul_ne_zero (sub_ne_zero.mpr rs.ne) (by linarith)
  constructor
  · rintro ⟨U,V,W,_,L,E⟩
    have nz (root:U=0 ∨ V=0 ∨ W=0) : False := out (one_of_boundary bp tp.ne' sp.ne' L E root)
    have un : U≠0:=fun q=>nz (Or.inl q)
    have vn : V≠0:=fun q=>nz (Or.inr (Or.inl q))
    have wn : W≠0:=fun q=>nz (Or.inr (Or.inr q))
    apply quotient_of_cover bp.ne' A (div_ne_zero un vn) (div_ne_zero wn (mul_ne_zero tp.ne' (pow_ne_zero 2 vn)))
    unfold singlePolynomial at E
    field_simp
    rw [←eq] at E
    linear_combination E
  · intro q
    obtain ⟨k,h,kn,hn,F⟩:=cover_of_quotient bp.ne' A q
    have den:k^2-b*1^2≠0:=by
      simp only [one_pow,mul_one]
      intro ne
      exact nonsquare ⟨k,by rw [←sq];exact (sub_eq_zero.mp ne).symm⟩
    refine ⟨k,1,θ*h,Or.inr one_ne_zero,den,?_⟩
    rw [formula eq]
    linear_combination θ^2*F

end
end Sun28.GlobalSections

#print axioms Sun28.GlobalSections.curve_discriminant
#print axioms Sun28.GlobalSections.quotient_of_cover
#print axioms Sun28.GlobalSections.cover_of_quotient
#print axioms Sun28.GlobalSections.single_iff_represented
