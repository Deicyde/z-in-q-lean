import NormQuartic

namespace Sun28.PointDescent
open PairedClasses PrescribedPoints TwistExtension TwistRank PreparedPoles

/-- The norm already supplied by Sun in the trace coordinates. -/
theorem trace_coordinates_of_preparation {b θ : ℕ} (w : NormConic b θ) :
    ∃ a c : ℚ, c≠0 ∧ a^2-θ*c^2=b := by
  obtain ⟨u,v,un,vn,E⟩:=w
  refine ⟨1/u,v/u,div_ne_zero vn un,?_⟩
  field_simp
  linear_combination -E

/-- The selected section cannot yield a two-torsion point on either target curve. -/
theorem nonzero_of_two_conics {b θ a c z : ℚ} (bp : 0<b) (tp : 0<θ) (cn : c≠0)
    (one : a^2-θ*c^2=b) (two : z^2=b+16*a^2/9) : NonzeroPair b θ := by
  have an : a≠0:=by rintro rfl; nlinarith [mul_pos tp (sq_pos_of_ne_zero cn)]
  have zn : z≠0:=by rintro rfl; nlinarith [sq_nonneg a]
  let L := -2*a/3
  have Ln : L≠0:=div_ne_zero (mul_ne_zero (by norm_num) an) (by norm_num)
  obtain ⟨l,ln,⟨u,y,un,yn,hy⟩,⟨v,q,vn,qn,hq⟩⟩:=marked_of_norm (L:=L) (h:=b*z)
    bp tp.ne' cn Ln (mul_ne_zero bp.ne' zn) one (by dsimp [L];linear_combination b^2*two)
  have reg : b≠L*(3*L+2*a) ∧ b≠3*L*(L-2*a) := by
    dsimp [L];constructor
    · intro H;apply bp.ne';linear_combination H
    · intro H;nlinarith [mul_pos tp (sq_pos_of_ne_zero cn),sq_nonneg a]
  exact ⟨l,u,v,y,q,ln,un,vn,yn reg,qn reg,hy,hq⟩

theorem nonzero_of_auxiliary {b θ : ℚ} (bp : 0<b) (tp : 0<θ)
    (cov : AuxiliaryCover b θ) : NonzeroPair b θ := by
  obtain ⟨k,w,kn,wn,H⟩:=cov
  apply nonzero_of_two_conics (a:=(k^2-9*b)/(8*k)) (c:=w/(8*k))
    (z:=(k^2+9*b)/(6*k)) bp tp (div_ne_zero wn (mul_ne_zero (by norm_num) kn))
  · field_simp
    linear_combination -H
  · field_simp
    ring

/-- Ordinary two-isogeny descent on one fixed curve, with its abscissa prescribed. -/
theorem auxiliary_iff_abscissa {b θ : ℚ} (tn : θ≠0) :
    AuxiliaryCover b θ ↔ ∃ k y : ℚ, k≠0 ∧ y≠0 ∧
      y^2=(θ*k^2)*(θ*k^2-b*θ)*(θ*k^2-81*b*θ) := by
  constructor
  · rintro ⟨k,w,kn,wn,H⟩
    exact ⟨k,θ^2*k*w,kn,mul_ne_zero (mul_ne_zero (pow_ne_zero 2 tn) kn) wn,
      by linear_combination θ^3*k^2*H⟩
  · rintro ⟨k,y,kn,yn,H⟩
    refine ⟨k,y/(θ^2*k),kn,div_ne_zero yn (mul_ne_zero (pow_ne_zero 2 tn) kn),?_⟩
    field_simp
    linear_combination H

/-- The remaining simultaneous assertion away from the explicit norm-quartic search. -/
def NormResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  ¬NormQuartic (b:ℚ) (θ:ℚ) → NonzeroPair (b:ℚ) (θ:ℚ)

theorem core_of_norm_residual (h : NormResidual) : CoreResidual := by
  intro b θ ad inp fixed conic factor one
  by_cases n : NormQuartic (b:ℚ) (θ:ℚ)
  · have bp : (0:ℚ)<b:=by exact_mod_cast ad.1
    have tp : (0:ℚ)<θ:=by exact_mod_cast ad.2.1
    exact ((surface_iff_one_or_nonzero bp tp.ne').mp (surface_of_norm_quartic bp tp.ne' n)).resolve_left one
  · exact h b θ ad inp fixed conic factor one n

theorem residual_iff_norm : CoreResidual ↔ NormResidual :=
  ⟨fun h b θ ad inp fixed conic factor one _=>h b θ ad inp fixed conic factor one,core_of_norm_residual⟩

end Sun28.PointDescent
#print axioms Sun28.PointDescent.trace_coordinates_of_preparation
#print axioms Sun28.PointDescent.nonzero_of_two_conics
#print axioms Sun28.PointDescent.nonzero_of_auxiliary
#print axioms Sun28.PointDescent.auxiliary_iff_abscissa
#print axioms Sun28.PointDescent.core_of_norm_residual
#print axioms Sun28.PointDescent.residual_iff_norm
