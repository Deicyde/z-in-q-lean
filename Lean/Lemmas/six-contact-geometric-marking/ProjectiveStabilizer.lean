import WeightedQuadratics
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Three independent quadratic covariants of the same bidegree kill the reduced
automorphism group. All identities are universal over a characteristic-zero field. -/
namespace ZInQBlueprint.MarkedForm
noncomputable section
variable {K : Type*} [Field K]

/-- Continued Gaussian elimination in two dimensions, using only a nonzero pivot. -/
theorem factor_matrix {a b c d : K} (hn : a*d-b*c≠0) :
    ∃ w : Word K, delta w=a*d-b*c ∧
      ∀ x z, point w x z=(a*x+b*z,c*x+d*z) := by
  by_cases hc : c=0
  · subst c
    have ha : a≠0 := by intro h; simp [h] at hn
    refine ⟨.comp (.shift (b/a)) (.comp (.diag a d) .one),?_,?_⟩
    · simp [delta,det]
    · intro x z
      simp [point,xy]
      field_simp
  · let Δ := a*d-b*c
    refine ⟨.comp (.shift (d/c)) (.comp (.diag c (-Δ/c)) (.comp .swap
      (.comp (.shift (a/c)) .one))),?_,?_⟩
    · dsimp [delta,det,Δ]
      field_simp
    · intro x z
      dsimp [point,xy,Δ]
      field_simp
      apply Prod.ext
      · apply (div_eq_iff hc).2
        ring
      · rfl

def veronese (x z : K) : Fin 3 → K := ![z^2,2*x*z,x^2]

private theorem dot_eval (q : Coeff K 2) (x z : K) :
    q ⬝ᵥ veronese x z=evalF q x z := by
  simp [dotProduct,veronese,evalF,Fin.sum_univ_succ,Fin.succ,Nat.choose]
  ring

/-- A projective symmetry is scalar as soon as the weighted three-row frame is invertible. -/
theorem trivial_stabilizer [CharZero K] [Infinite K] (f : Coeff K 6)
    (hf : (Matrix.det (rows f : Matrix (Fin 3) (Fin 3) K))≠0)
    {a b c d μ : K} (hM : a*d-b*c≠0)
    (action : ∀ x z, evalF f (a*x+b*z) (c*x+d*z)=μ*evalF f x z) :
    b=0 ∧ c=0 ∧ a=d := by
  obtain ⟨w,hd,hp⟩ := factor_matrix hM
  have hΔ : delta w≠0 := hd.trans_ne hM
  have eq : sexticAction w f=scale μ f := by
    apply ext_form
    intro x z
    rw [sextic_action_eval,hp,eval_scale,action]
  let R : Matrix (Fin 3) (Fin 3) K := rows f
  let κ := μ^7/(delta w)^20
  have frame (x z : K) :
      veronese (a*x+b*z) (c*x+d*z)=κ • veronese x z := by
    apply Matrix.mulVec_injective_of_det_ne_zero (M:=R) hf
    rw [Matrix.mulVec_smul]
    funext i
    change (rows f i) ⬝ᵥ veronese (a*x+b*z) (c*x+d*z)=κ*((rows f i) ⬝ᵥ veronese x z)
    rw [dot_eval,dot_eval]
    have he := row_action_eval w f i x z
    rw [eq,rows_scale,eval_scale,hp] at he
    change _=μ^7/(delta w)^20*_ 
    rw [div_mul_eq_mul_div,eq_div_iff (pow_ne_zero _ hΔ)]
    linear_combination -he
  have hb₂ := congrFun (frame 0 1) 2
  have hc₂ := congrFun (frame 1 0) 0
  change (a*0+b*1)^2=κ*(0:K)^2 at hb₂
  change (c*1+d*0)^2=κ*(0:K)^2 at hc₂
  simp at hb₂ hc₂
  subst b; subst c
  refine ⟨rfl,rfl,?_⟩
  have haa : a≠0 := by intro h; simp [h] at hM
  have had := congrFun (frame 1 1) 1
  have has := congrFun (frame 1 0) 2
  change 2*(a*1+0*1)*(0*1+d*1)=κ*(2*1*1) at had
  change (a*1+0*0)^2=κ*(1:K)^2 at has
  have equal : a*(a-d)=0 := by
    linear_combination has - had/2
  exact sub_eq_zero.mp ((mul_eq_zero.mp equal).resolve_left haa)

end
end ZInQBlueprint.MarkedForm

#print axioms ZInQBlueprint.MarkedForm.factor_matrix
#print axioms ZInQBlueprint.MarkedForm.trivial_stabilizer
