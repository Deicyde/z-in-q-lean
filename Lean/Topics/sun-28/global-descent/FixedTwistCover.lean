import GlobalSections

namespace Sun28.GlobalDescent
open Sun28.PairedClasses Sun28.PreparedPoles
noncomputable section

/-- Both homogeneous directions are retained. On the affine chart V=1,
the equation is Y²=d (U²-b)(U²+3b). -/
def KernelCover (b d:ℕ) : Prop := ∃u v y:ℚ,(u≠0 ∨ v≠0) ∧
  y^2=(d:ℚ)*quartic b u v

theorem fixed_twist_iff_cover {b d:ℕ} (bp:0<b) (dp:0<d) (ns:¬IsSquare (b:ℚ)) :
    TwistPoint b (b*d) ↔ KernelCover b d := by
  have B : (b:ℚ)≠0:=by exact_mod_cast bp.ne'
  have D : (d:ℚ)≠0:=by exact_mod_cast dp.ne'
  rw [twist_iff_quartic bp (Nat.mul_pos bp dp)]
  constructor
  · rintro ⟨u,v,w,e⟩
    push_cast at e
    have q:(d:ℚ)=quartic b u v*w^2:=by
      apply mul_left_cancel₀ B
      linear_combination e
    have coords:u≠0 ∨ v≠0:=by
      by_contra! zero
      rw [zero.1,zero.2] at q
      simp [quartic] at q
      exact dp.ne' q
    refine ⟨u,v,quartic b u v*w,coords,?_⟩
    linear_combination -(quartic b u v)*q
  · rintro ⟨u,v,y,uv,e⟩
    by_cases zero:y=0
    · have q:quartic b u v=0:=(mul_eq_zero.mp (by simpa [zero] using e.symm)).resolve_left D
      unfold quartic at q
      rcases mul_eq_zero.mp q with q|q
      · have vn:v≠0:=by
          rintro rfl
          have un:=uv.resolve_right (by simp)
          simp [un] at q
        have sq:(b:ℚ)=(u/v)^2:=by field_simp;linear_combination -q
        exact False.elim (ns ⟨u/v,by simpa [pow_two] using sq⟩)
      · have pos:0<u^2+3*(b:ℚ)*v^2:=by
          rcases uv with h|h
          · have : 0<u^2:=sq_pos_of_ne_zero h
            positivity
          · have : 0<v^2:=sq_pos_of_ne_zero h
            have : 0<(b:ℚ):=by exact_mod_cast bp
            positivity
        exact False.elim (pos.ne' q)
    · refine ⟨u,v,(d:ℚ)/y,?_⟩
      push_cast;field_simp
      linear_combination e

end
end Sun28.GlobalDescent
#print axioms Sun28.GlobalDescent.fixed_twist_iff_cover
