import ProjectiveStabilizer
import SexticIgusaPole

/-! The quadratic invariant in ordinary coefficients, including forms with
vanishing leading coefficient. Coordinate changes act on the homogeneous sextic. -/
namespace ZInQBlueprint.MinimalDiscriminant
open MarkedForm Polynomial JacobianHeight
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Ordinary coefficients, in ascending powers of the first variable. -/
abbrev Coefficients (R : Type*) := Fin 7 → R

def form (f : Coefficients K) (x z : K) : K :=
  ∑ i : Fin 7, f i * x^i.val * z^(6-i.val)

def fourJ2 {R : Type*} [CommRing R] (f : Coefficients R) : R :=
  -120*f 0*f 6 + 20*f 1*f 5 - 8*f 2*f 4 + 3*(f 3)^2

theorem fourJ2_map {R S : Type*} [CommRing R] [CommRing S] (m : R →+* S)
    (f : Coefficients R) : fourJ2 (fun i => m (f i)) = m (fourJ2 f) := by
  norm_num [fourJ2, map_ofNat]

private def binomial (f : Coefficients K) : Coeff K 6 := fun i => f i / (Nat.choose 6 i.val : K)

private theorem form_binomial (f : Coefficients K) (x z : K) :
    evalF (binomial f) x z = form f x z := by
  unfold evalF form
  apply Finset.sum_congr rfl
  intro i _
  have h : (Nat.choose 6 i.val : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : i.val ≤ 6)).ne'
  unfold binomial
  field_simp

private theorem binomial_invariant (f : Coefficients K) :
    fourJ2 f = -60 * invariant (binomial f) := by
  norm_num [fourJ2, binomial, invariant, Nat.choose]
  ring

omit [CharZero K] in
private theorem invariant_word (w : Word K) (f : Coeff K 6) :
    invariant (sexticAction w f) = (delta w)^6 * invariant f := by
  induction w with
  | one => simp [delta,sexticAction]
  | comp g w ih => rw [sexticAction,invariant_cov,ih,delta,mul_pow,mul_assoc]

/-- The substitution includes both the base coordinate and the scalar of the form. -/
theorem fourJ2_change (f g : Coefficients K) (a b c d s : K) (hM : a*d-b*c ≠ 0)
    (equation : ∀ x z, form g x z = s * form f (a*x+b*z) (c*x+d*z)) :
    fourJ2 g = s^2*(a*d-b*c)^6*fourJ2 f := by
  obtain ⟨w,hd,hp⟩ := factor_matrix hM
  have h : binomial g = scale s (sexticAction w (binomial f)) := by
    apply ext_form
    intro x z
    rw [form_binomial,eval_scale,sextic_action_eval,hp,form_binomial]
    exact equation x z
  rw [binomial_invariant g,binomial_invariant f,h,invariant_scale,invariant_word,hd]
  ring

theorem rational_fourJ2 (f : ℚ[X]) : fourJ2 (fun i => f.coeff i.val) = 4*igusaJ2 f := by
  rw [liu_quadratic]
  dsimp [fourJ2]
  ring

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.fourJ2_map
#print axioms ZInQBlueprint.MinimalDiscriminant.fourJ2_change
#print axioms ZInQBlueprint.MinimalDiscriminant.rational_fourJ2
