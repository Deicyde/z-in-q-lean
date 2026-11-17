import ProductClasses

/-! Keep the choice of the listed multiplier until after seeking a point. -/
namespace Sun28.MultiplierChoice
open Sun28.TwistExtension Sun28.Ordinary Sun28.ScalarHeight
noncomputable section

def Pair (b t : ℚ) : Prop := ∃ l:ℚ, l≠0 ∧ Point b l ∧ Point b (l*t)

private theorem mark_scale {b l c:ℚ} (cn:c≠0) : Point (b*c^2) l ↔ Point b l := by
  constructor
  · rintro ⟨u,y,un,h⟩
    exact ⟨c*u,y,mul_ne_zero cn un,by convert h using 1; ring⟩
  · rintro ⟨u,y,un,h⟩
    exact ⟨u/c,y,div_ne_zero un cn,by convert h using 1; field_simp [cn]⟩

private theorem twist_scale {b l c:ℚ} (cn:c≠0) : Point b (l*c^2) ↔ Point b l := by
  refine ⟨fun p=>?_,point_scale cn⟩
  have q:=point_scale (inv_ne_zero cn) p
  rw [show l*c^2*c⁻¹^2=l by field_simp] at q
  exact q

theorem pair_mark_scale {b t c:ℚ} (cn:c≠0) : Pair (b*c^2) t ↔ Pair b t := by
  unfold Pair
  simp only [mark_scale cn]

theorem pair_twist_scale {b t c:ℚ} (cn:c≠0) : Pair b (t*c^2) ↔ Pair b t := by
  unfold Pair
  simp only [←mul_assoc,twist_scale cn]

/-- Sun's two original guarded equations are equivalent for arbitrary signed A to
two abscissa tests on distinct twists. The second twist has normalized ratio 1-B/μ. -/
theorem branch_iff_pair {μ B:ℚ} (mn:μ≠0) (bn:B≠0) (different:B≠μ) :
    (∃e z:ℚ,poleBranch μ B e z) ↔ Pair (μ*B) (1-B/μ) := by
  let A:=μ*B
  let H:=A*(A-B^2)
  have an:A≠0:=mul_ne_zero mn bn
  have form : H=A^2*(1-B/μ) := by dsimp [H,A];field_simp [mn]
  have tn : 1-B/μ≠0 := by
    intro h;apply different;field_simp [mn] at h;linarith
  have hn:H≠0:=form ▸ mul_ne_zero (pow_ne_zero 2 an) tn
  rw [←pair_twist_scale (b:=A) (t:=1-B/μ) an, mul_comm (1-B/μ),←form]
  constructor
  · rintro ⟨e,z,guard,y,Y,p,q⟩
    change A*e*H*z≠0 at guard
    have zn:=right_ne_zero_of_mul guard
    have en:=right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul guard))
    refine ⟨e,en,⟨1,y,one_ne_zero,by simpa [A] using p⟩,z,z*Y,zn,?_⟩
    change Y^2=A*(A*z^2-e*H)*(A*z^2+3*e*H) at q
    linear_combination z^2*q
  · rintro ⟨l,ln,⟨u,y,un,p⟩,v,Y,vn,q⟩
    let e:=l/u^2
    let z:=v/u
    refine ⟨e,z,mul_ne_zero (mul_ne_zero (mul_ne_zero an (div_ne_zero ln (pow_ne_zero 2 un))) hn)
      (div_ne_zero vn un),y/u^3,Y/(u^2*v),?_,?_⟩
    · change (y/u^3)^2=A*(A-l/u^2)*(A+3*(l/u^2))
      field_simp [un];linear_combination p
    · change (Y/(u^2*v))^2=A*(A*(v/u)^2-l/u^2*H)*(A*(v/u)^2+3*(l/u^2)*H)
      field_simp [un,vn];linear_combination q

/-- Translation by (0,0) interchanges the nonzero abscissa classes b and −3b.
This remains valid at the other two points of order two. -/
private theorem swap_mark {b l:ℚ} (bn:b≠0) (ln:l≠0) (P:Point b l) : Point (-3*b) l := by
  obtain ⟨u,y,un,h⟩:=P
  refine ⟨l/(b*u),3*l^2*y/(b*u^2)^2,div_ne_zero ln (mul_ne_zero bn un),?_⟩
  field_simp [bn,un]
  linear_combination h

theorem marks_iff {b l:ℚ} (bn:b≠0) (ln:l≠0) : Point (-3*b) l ↔ Point b l := by
  refine ⟨fun p=>?_,swap_mark bn ln⟩
  have q:=swap_mark (mul_ne_zero (by norm_num : (-3:ℚ)≠0) bn) ln p
  rw [show (-3:ℚ)*(-3*b)=b*3^2 by ring] at q
  exact (mark_scale (by norm_num : (3:ℚ)≠0)).mp q

theorem pair_marks {b t:ℚ} (bn:b≠0) (tn:t≠0) : Pair (-3*b) t ↔ Pair b t := by
  constructor
  · rintro ⟨l,ln,p,q⟩
    exact ⟨l,ln,(marks_iff bn ln).mp p,(marks_iff bn (mul_ne_zero ln tn)).mp q⟩
  · rintro ⟨l,ln,p,q⟩
    exact ⟨l,ln,(marks_iff bn ln).mpr p,(marks_iff bn (mul_ne_zero ln tn)).mpr q⟩

end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.pair_mark_scale
#print axioms Sun28.MultiplierChoice.pair_twist_scale
#print axioms Sun28.MultiplierChoice.branch_iff_pair
#print axioms Sun28.MultiplierChoice.marks_iff
#print axioms Sun28.MultiplierChoice.pair_marks
