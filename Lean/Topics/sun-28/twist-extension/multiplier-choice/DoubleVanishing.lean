import PoleTwistChoice

namespace Sun28.MultiplierChoice
open Sun28.Ordinary
noncomputable section

def DoubleRoot (μ B : ℚ) : Prop := ∃e z : ℚ,
  let A:=μ*B
  let H:=A*(A-B^2)
  A*e*H*z≠0 ∧ A*(A-e)*(A+3*e)=0 ∧
    A*(A*z^2-e*H)*(A*z^2+3*e*H)=0

theorem double_accepted {μ B:ℚ} (r:DoubleRoot μ B) : ∃e z:ℚ,poleBranch μ B e z := by
  obtain ⟨e,z,n,h,g⟩:=r
  exact ⟨e,z,n,0,0,by simpa using h.symm,by simpa using g.symm⟩

/-- Exactly which pole arguments admit certificates with both ordinates zero. -/
theorem double_root_iff {μ B:ℚ} (mn:μ≠0) (bn:B≠0) (diff:B≠μ) :
    DoubleRoot μ B ↔ IsSquare (1-B/μ) ∨ IsSquare (-3*(1-B/μ)) := by
  let A:=μ*B
  let H:=A*(A-B^2)
  let t:=1-B/μ
  have an:A≠0:=mul_ne_zero mn bn
  have tn:t≠0:=by dsimp [t];intro h;apply diff;field_simp [mn] at h;linarith
  have form:H=A^2*t:=by dsimp [H,A,t];field_simp [mn]
  have hn:H≠0:=form ▸ mul_ne_zero (pow_ne_zero 2 an) tn
  have W {z k:ℚ} (h:z^2=H*k) : IsSquare (k*t) := by
    refine ⟨z/A,?_⟩
    rw [←sq,div_pow,eq_div_iff (pow_ne_zero 2 an),h,form];ring
  constructor
  · rintro ⟨e,z,_,p,q⟩
    change A*(A-e)*(A+3*e)=0 at p
    change A*(A*z^2-e*H)*(A*z^2+3*e*H)=0 at q
    have h : A=e ∨ A= -3*e := by
      rcases mul_eq_zero.mp p with p|p
      · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp p).resolve_left an))
      · exact Or.inr (by linarith)
    rw [mul_assoc] at q
    have q' := (mul_eq_zero.mp q).resolve_left an
    rcases h with h|h
    · rw [←h] at q'
      rcases mul_eq_zero.mp q' with a|b
      · left
        suffices hv : z^2=H*1 by simpa using W hv
        apply mul_left_cancel₀ an
        linear_combination a
      · right;apply W (z:=z)
        apply mul_left_cancel₀ an
        linear_combination b
    · have en:e≠0:=by intro e0;apply an;rw [h,e0];ring
      rw [h] at q'
      rcases mul_eq_zero.mp q' with a|b
      · right; apply W (z:=3*z)
        apply mul_left_cancel₀ en
        linear_combination -3*a
      · left
        have root:z^2=H*1:=by
          apply mul_left_cancel₀ en
          linear_combination -b/3
        simpa using W root
  · rintro (⟨u,root⟩|⟨u,root⟩)
    · change t=u*u at root
      have un:u≠0:=by intro h;apply tn;rw [root,h];ring
      refine ⟨A,A*u,mul_ne_zero (mul_ne_zero (mul_ne_zero an an) hn) (mul_ne_zero an un),?_,?_⟩
      · change A*(A-A)*(A+3*A)=0;ring
      · change A*(A*(A*u)^2-A*H)*(A*(A*u)^2+3*A*H)=0
        rw [form,root];ring
    · change -3*t=u*u at root
      have un:u≠0:=by intro h;apply tn;rw [h] at root;linarith
      refine ⟨A,A*u,mul_ne_zero (mul_ne_zero (mul_ne_zero an an) hn) (mul_ne_zero an un),?_,?_⟩
      · change A*(A-A)*(A+3*A)=0;ring
      · change A*(A*(A*u)^2-A*H)*(A*(A*u)^2+3*A*H)=0
        rw [form];have g:u^2= -3*t:=by rw [sq];exact root.symm
        have z:A*(A*u)^2+3*A*(A^2*t)=0:=by linear_combination A^3*g
        rw [z,mul_zero]
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.double_accepted
#print axioms Sun28.MultiplierChoice.double_root_iff
