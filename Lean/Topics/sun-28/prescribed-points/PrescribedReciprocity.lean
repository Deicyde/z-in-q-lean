import FamilyLocal
namespace Sun28.PrescribedPoints
open PairedClasses
noncomputable section

theorem reciprocal_identity {b θ s h : ℚ} (hn : h≠0)
    (eq : (s^2-b)*(9*s^2-b)=θ*h^2) :
    let k := (s^2-b)/h
    (k^2-θ)*(9*k^2-θ)=b*(8*s*(s^2-b)/h^2)^2 := by
  dsimp only
  have a : ((s^2-b)/h)^2-θ=(-8*s^2*(s^2-b))/h^2 := by
    field_simp
    linear_combination eq
  have c : 9*((s^2-b)/h)^2-θ=(-8*b*(s^2-b))/h^2 := by
    field_simp
    linear_combination eq
  rw [a,c]
  ring

theorem reciprocal_family {b θ : ℕ} (tp : 0<θ) {s h : ℚ} (sn : s≠0) (hn : h≠0)
    (eq : (s^2-b)*(9*s^2-b)=(θ:ℚ)*h^2) : Family θ b := by
  have f : s^2-b≠0 := left_ne_zero_of_mul
    (show (s^2-b)*(9*s^2-b)≠0 from eq ▸ mul_ne_zero (by exact_mod_cast tp.ne') (pow_ne_zero 2 hn))
  exact ⟨(s^2-b)/h,8*s*(s^2-b)/h^2,div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) sn) f)
    (pow_ne_zero _ hn),reciprocal_identity hn eq⟩
end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.reciprocal_identity
#print axioms Sun28.PrescribedPoints.reciprocal_family
