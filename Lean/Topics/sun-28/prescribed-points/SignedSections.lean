import ProductClasses

namespace Sun28.PrescribedPoints
open PairedClasses TwistExtension
noncomputable section

def OneQuartic (b θ : ℚ) : Prop := ∃ u v z : ℚ,
  θ = quartic b u v*z^2 ∨ -3*θ = quartic b u v*z^2

def NonzeroPair (b θ : ℚ) : Prop := ∃ l u v y z : ℚ,
  l≠0 ∧ u≠0 ∧ v≠0 ∧ y≠0 ∧ z≠0 ∧
  y^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l) ∧
  z^2=(b*v^2)*(b*v^2-l*θ)*(b*v^2+3*(l*θ))

theorem one_quartic_iff {b θ : ℚ} (bp : 0<b) (tn : θ≠0) :
    OneQuartic b θ ↔ Point b (b*θ) ∨ Point b ((-3*b)*θ) := by
  rw [point_quartic bp (mul_ne_zero bp.ne' tn),
      point_quartic bp (mul_ne_zero (mul_ne_zero (by norm_num) bp.ne') tn)]
  constructor
  · rintro ⟨u,v,z,pos|neg⟩
    · exact Or.inl ⟨u,v,z,by linear_combination b*pos⟩
    · exact Or.inr ⟨u,v,z,by linear_combination b*neg⟩
  · rintro (⟨u,v,z,h⟩|⟨u,v,z,h⟩)
    · exact ⟨u,v,z,Or.inl (by apply mul_left_cancel₀ bp.ne';linear_combination h)⟩
    · exact ⟨u,v,z,Or.inr (by apply mul_left_cancel₀ bp.ne';linear_combination h)⟩

theorem surface_of_one_quartic {b θ : ℚ} (bp : 0<b) (tn : θ≠0) (test : OneQuartic b θ) :
    Surface b θ := by
  apply (surface_iff_pair bp tn).mpr
  rcases (one_quartic_iff bp tn).mp test with pos|neg
  · exact ⟨b,bp.ne',⟨1,0,one_ne_zero,by ring⟩,pos⟩
  · exact ⟨-3*b,mul_ne_zero (by norm_num) bp.ne',⟨3,0,by norm_num,by ring⟩,neg⟩

private theorem zero_twist {b l u : ℚ} (bn : b≠0) (un : u≠0)
    (e : (0:ℚ)^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l)) :
    ∃ r : ℚ,r≠0 ∧ (l=b*r^2 ∨ l=(-3*b)*r^2) := by
  have x : b*u^2≠0 := mul_ne_zero bn (pow_ne_zero _ un)
  have P : (b*u^2)*(b*u^2-l)*(b*u^2+3*l)=0 := by simpa using e.symm
  rcases mul_eq_zero.mp P with one|two
  · exact ⟨u,un,Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp one).resolve_left x)).symm⟩
  · exact ⟨u/3,div_ne_zero un (by norm_num),Or.inr (by linear_combination two/3)⟩

private theorem restore {b c r θ l : ℚ} (rn : r≠0) (eq : l=c*r^2)
    (pt : Point b (l*θ)) : Point b (c*θ) := by
  have scaled := point_scale (inv_ne_zero rn) pt
  rw [eq,show c*r^2*θ*r⁻¹^2=c*θ by field_simp] at scaled
  exact scaled

theorem surface_iff_one_or_nonzero {b θ : ℚ} (bp : 0<b) (tn : θ≠0) :
    Surface b θ ↔ OneQuartic b θ ∨ NonzeroPair b θ := by
  constructor
  · intro s
    obtain ⟨l,ln,⟨u,y,un,one⟩,⟨v,z,vn,two⟩⟩ := (surface_iff_pair bp tn).mp s
    by_cases yz : y=0
    · subst y
      left
      apply (one_quartic_iff bp tn).mpr
      obtain ⟨r,rn,e|e⟩:=zero_twist bp.ne' un one
      · exact Or.inl (restore rn e ⟨v,z,vn,two⟩)
      · exact Or.inr (restore rn e ⟨v,z,vn,two⟩)
    by_cases zz : z=0
    · subst z
      left
      apply (one_quartic_iff bp tn).mpr
      have swap : Point b ((l*θ)*θ) := by
        have pt := point_scale tn (show Point b l from ⟨u,y,un,one⟩)
        convert pt using 1; ring
      obtain ⟨r,rn,e|e⟩:=zero_twist bp.ne' vn two
      · exact Or.inl (restore rn e swap)
      · exact Or.inr (restore rn e swap)
    · exact Or.inr ⟨l,u,v,y,z,ln,un,vn,yz,zz,one,two⟩
  · rintro (h|⟨l,u,v,y,z,ln,un,vn,_,_,a,c⟩)
    · exact surface_of_one_quartic bp tn h
    · exact (surface_iff_pair bp tn).mpr ⟨l,ln,⟨u,y,un,a⟩,v,z,vn,c⟩

/-- A single quartic in k gives the negative twist with its first point of order two. -/
theorem negative_section {b θ k h : ℚ} (hn : h≠0)
    (eq : (b-9*k^2)*(b+3*k^2)=θ*h^2) : OneQuartic b θ := by
  refine ⟨3*k,1,h⁻¹,Or.inr ?_⟩
  unfold quartic
  field_simp
  linear_combination eq
end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.one_quartic_iff
#print axioms Sun28.PrescribedPoints.surface_of_one_quartic
#print axioms Sun28.PrescribedPoints.surface_iff_one_or_nonzero
#print axioms Sun28.PrescribedPoints.negative_section
