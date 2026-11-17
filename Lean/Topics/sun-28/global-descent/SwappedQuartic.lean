import OrbitResidual

namespace Sun28.GlobalDescent
open Sun28.PairedClasses Sun28.PrescribedPoints Sun28.PointFibres Sun28.PreparedPoles
  Sun28.GlobalSections Sun28.TwistRank Sun28.TwistExtension Sun28.PointLifts
noncomputable section

private theorem choose_class {d f y:ℚ} (yn:y≠0) (p:d*f=y^2) : d=f*(d/y)^2 := by
  field_simp
  linear_combination -d*p

private theorem affine_normalize {t d u v z:ℚ} (vn:v≠0) (p:d=quartic t u v*z^2) :
    d=(|u/v|^2-t)*(|u/v|^2+3*t)*(v^2*z)^2 := by
  rw [p,sq_abs]; unfold quartic
  field_simp

private theorem reciprocal_factor {t k:ℚ} (kn:k≠0) :
    (t-(t/k)^2)*(3*(t/k)^2+t)=(k^2-t)*(k^2+3*t)*(t/k^2)^2 := by
  field_simp
  ring

/-- The physical sections are the original homogeneous one-quartic test in reversed order. -/
theorem physical_iff_transposed {b θ:ℕ} (bp:0<(b:ℚ)) (tp:0<(θ:ℚ)) (ns:¬IsSquare (b:ℚ)) :
    SectionHit b θ ↔ OneQuartic (θ:ℚ) b := by
  constructor
  · rintro ⟨s,_,short,⟨k,e⟩|⟨k,e⟩⟩
    · have pos : 0<(b:ℚ)*(θ-s^2)*(3*s^2+θ):=by positivity [sub_pos.mpr short]
      have kn:k≠0:=by rintro rfl; nlinarith only [e,pos]
      refine ⟨θ,s,(b:ℚ)/(θ*k),Or.inl (choose_class (mul_ne_zero tp.ne' kn) ?_)⟩
      unfold quartic
      linear_combination (θ:ℚ)^2*e
    · have pos : 0<3*(b:ℚ)*(θ-s^2)*(s^2+3*θ):=by positivity [sub_pos.mpr short]
      have kn:k≠0:=by rintro rfl; nlinarith only [e,pos]
      refine ⟨s,1,-3*(b:ℚ)/k,Or.inr (choose_class kn ?_)⟩
      unfold quartic
      linear_combination e
  · rintro ⟨u,v,z,h⟩
    have vn:v≠0:=by
      rintro rfl; rcases h with e|e
      · apply ns; refine ⟨u^2*z,?_⟩; unfold quartic at e; linear_combination e
      · unfold quartic at e; nlinarith only [e,sq_nonneg (u^2*z),bp]
    have un:u≠0:=by
      rintro rfl; rcases h with e|e
      · unfold quartic at e; nlinarith only [e,sq_nonneg ((θ:ℚ)*v^2*z),bp]
      · apply ns; refine ⟨(θ:ℚ)*v^2*z,?_⟩; unfold quartic at e; linear_combination -e/3
    let k:=|u/v|
    let w:=v^2*z
    have kp:0<k:=abs_pos.mpr (div_ne_zero un vn)
    have nonneg:0≤(k^2+3*(θ:ℚ))*w^2:=by positivity
    rcases h with h|h
    · have e:(b:ℚ)=(k^2-θ)*(k^2+3*θ)*w^2:=affine_normalize vn h
      have gt:0<k^2-(θ:ℚ):=by
        by_contra! hh
        nlinarith only [mul_nonpos_of_nonpos_of_nonneg hh nonneg,e,bp]
      have short:((θ:ℚ)/k)^2<θ:=by
        rw [div_pow,div_lt_iff₀ (sq_pos_of_pos kp)]
        nlinarith only [mul_pos tp gt]
      let f:=(k^2-(θ:ℚ))*(k^2+3*θ)
      have sq:(b:ℚ)*f=(f*w)^2:=by change (b:ℚ)=f*w^2 at e; rw [e];ring
      refine ⟨θ/k,div_pos tp kp,short,Or.inl ⟨f*w*((θ:ℚ)/k^2),?_⟩⟩
      calc
        (b:ℚ)*(θ-(θ/k)^2)*(3*(θ/k)^2+θ) = b*((θ-(θ/k)^2)*(3*(θ/k)^2+θ)) := by ring
        _ = ((b:ℚ)*f)*((θ:ℚ)/k^2)^2 := by rw [reciprocal_factor kp.ne'];dsimp [f]; ring
        _ = _ := by rw [sq];ring
    · have e:-3*(b:ℚ)=(k^2-θ)*(k^2+3*θ)*w^2:=affine_normalize vn h
      have short:k^2<θ:=by
        by_contra! hh
        nlinarith only [mul_nonneg (sub_nonneg.mpr hh) nonneg,e,bp]
      let f:=(k^2-(θ:ℚ))*(k^2+3*θ)
      have sq:(-3*(b:ℚ))*f=(f*w)^2:=by change -3*(b:ℚ)=f*w^2 at e; rw [e];ring
      refine ⟨k,kp,short,Or.inr ⟨f*w,?_⟩⟩
      dsimp [f] at *
      linear_combination sq

theorem section_iff_transposed {b θ:ℕ} (a:AdmissiblePair b θ) :
    SectionHit b θ ↔ OneQuartic (θ:ℚ) b := by
  have bp:0<(b:ℚ):=by exact_mod_cast a.1
  apply physical_iff_transposed bp (by exact_mod_cast a.2.1)
  rintro ⟨k,h⟩
  have kn:k≠0:=by rintro rfl;nlinarith only [h,bp]
  exact ((regular_base a) (1/k) (one_div_ne_zero kn)).1 (by field_simp;linear_combination h)

/-- Both signed quartic tests use the same polynomial. They are evaluated in each input order. -/
def TransposedResidual : Prop := ∀ b θ:ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) θ →
  (∀ t:ℚ,t≠0 → ¬RatioCover (b:ℚ) θ t) → ¬CancelledFactors b θ → ¬OneQuartic (θ:ℚ) b →
  ∃ s:ℚ, 0<s ∧ s^2<θ ∧ AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧
    ¬KnownOrbit (s^2/θ) (b*lead (s^2/θ)) ∧ represented b (s^2/θ)

theorem sections_iff_transposed_residual : SectionResidual ↔ TransposedResidual := by
  rw [sections_iff_descent]
  constructor
  · intro H b θ a input fixed norm fac one pencil cancel other
    exact H b θ a input fixed norm fac one pencil cancel (other ∘ (section_iff_transposed a).mp)
  · intro H b θ a input fixed norm fac one pencil cancel other
    exact H b θ a input fixed norm fac one pencil cancel (other ∘ (section_iff_transposed a).mpr)

end
end Sun28.GlobalDescent
#print axioms Sun28.GlobalDescent.physical_iff_transposed
#print axioms Sun28.GlobalDescent.section_iff_transposed
#print axioms Sun28.GlobalDescent.sections_iff_transposed_residual
