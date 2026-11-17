import QuarticReciprocity

/-! The two coefficient orders for the homogeneous signed quartic give the same test. -/
namespace Sun28.CommonPair
open Sun28.PairedClasses Sun28.PrescribedPoints
noncomputable section

private theorem affine_of_homogeneous {k b d : ℚ} (kn:k≠0) (dn:d≠0) (dns:¬IsSquare d)
    (sign : k=1 ∨ k=-3) (dp:0<d) {u v w : ℚ}
    (h : k*d=quartic b u v*w^2) :
    ∃P : ℚ×ℚ, P.2≠0 ∧ OnQuartic k b d P := by
  have vn : v≠0 := by
    rintro rfl
    rcases sign with rfl|rfl
    · apply dns;refine ⟨u^2*w,?_⟩;unfold quartic at h;linear_combination h
    · unfold quartic at h
      nlinarith only [h,dp,sq_nonneg (u^2*w)]
  have wn : w≠0 := by
    rintro rfl
    exact mul_ne_zero kn dn (by simpa using h)
  let x:=u/v
  have e : k*d=(x^2-b)*(x^2+3*b)*(v^2*w)^2 := by
    dsimp [x];unfold quartic at h
    field_simp [vn]; linear_combination h
  let y:= k*d/(v^2*w)
  refine ⟨(x,y),div_ne_zero (mul_ne_zero kn dn) (mul_ne_zero (pow_ne_zero 2 vn) wn),?_⟩
  change y^2=k*d*(x^2-b)*(x^2+3*b)
  dsimp [y];field_simp [vn,wn]
  linear_combination e

private theorem homogeneous_of_affine {k b d : ℚ} {P : ℚ×ℚ} (point:OnQuartic k b d P)
    (yn:P.2≠0) :
    ∃u v w : ℚ, k*d=quartic b u v*w^2 := by
  refine ⟨P.1,1,k*d/P.2,?_⟩
  unfold OnQuartic at point
  unfold quartic
  field_simp [yn]
  linear_combination k*d*point

private theorem swap_direction {b d k : ℚ} (bp:0<b) (dp:0<d) (dns:¬IsSquare d)
    (sign:k=1 ∨ k=-3) {u v w : ℚ} (h:k*d=quartic b u v*w^2) :
    ∃u v w : ℚ, k*b=quartic d u v*w^2 := by
  have kn : k≠0 := by rcases sign with rfl|rfl <;> norm_num
  obtain ⟨⟨x,y⟩,yn,pt⟩:=affine_of_homogeneous kn dp.ne' dns sign dp h
  change y≠0 at yn
  have xnz:x≠0 := by
    rintro rfl
    rcases sign with rfl|rfl
    · change y^2=1*d*(0^2-b)*(0^2+3*b) at pt
      nlinarith only [pt,sq_nonneg y,mul_pos dp (sq_pos_of_pos bp)]
    · apply dns;refine ⟨y/(3*b),?_⟩
      change y^2=(-3)*d*(0^2-b)*(0^2+3*b) at pt
      field_simp;linear_combination -pt
  rcases sign with rfl|rfl
  · have den : x^2-b≠0 := by
      intro z;apply yn
      have t:=pt
      change y^2=1*d*(x^2-b)*(x^2+3*b) at t
      rw [z] at t;nlinarith only [t]
    exact homogeneous_of_affine (pos_involution bp.ne' dp.ne' pt den).1
      (div_ne_zero (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) bp.ne') dp.ne') xnz) den)
  · have den : x^2+3*b≠0 := by positivity
    exact homogeneous_of_affine (neg_involution bp.ne' dp.ne' pt den).1
      (div_ne_zero (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) bp.ne') dp.ne') xnz) den)

/-- Both signed factors are preserved individually when the two inputs are positive nonsquares. -/
theorem signed_symmetry {b d k : ℚ} (bp:0<b) (dp:0<d) (bs:¬IsSquare b) (ds:¬IsSquare d)
    (sign : k=1 ∨ k=-3) :
    (∃u v w : ℚ, k*d=quartic b u v*w^2) ↔ (∃u v w : ℚ, k*b=quartic d u v*w^2) := by
  constructor
  · rintro ⟨u,v,w,h⟩;exact swap_direction bp dp ds sign h
  · rintro ⟨u,v,w,h⟩;exact swap_direction dp bp bs sign h

theorem one_symmetry {b d : ℚ} (bp:0<b) (dp:0<d) (bs:¬IsSquare b) (ds:¬IsSquare d) :
    OneQuartic b d ↔ OneQuartic d b := by
  have parts (a c:ℚ) : OneQuartic a c ↔
      (∃u v w : ℚ, 1*c=quartic a u v*w^2) ∨ (∃u v w : ℚ, (-3)*c=quartic a u v*w^2) := by
    simp only [OneQuartic,one_mul]
    constructor
    · rintro ⟨u,v,w,h|h⟩
      · exact Or.inl ⟨u,v,w,h⟩
      · exact Or.inr ⟨u,v,w,h⟩
    · rintro (⟨u,v,w,h⟩|⟨u,v,w,h⟩)
      · exact ⟨u,v,w,Or.inl h⟩
      · exact ⟨u,v,w,Or.inr h⟩
  rw [parts b d,parts d b]
  exact or_congr (signed_symmetry bp dp bs ds (Or.inl rfl)) (signed_symmetry bp dp bs ds (Or.inr rfl))

end
end Sun28.CommonPair
#print axioms Sun28.CommonPair.signed_symmetry
#print axioms Sun28.CommonPair.one_symmetry
