import QuaternionOrder

/-! Polarized automorphisms of the discriminant-six order.
In the printed lattice the scalar part of the Rosati product is a
positive integral quadratic form divided by four. -/
namespace ZInQBlueprint.RosatiSigns
open LevelThree QuaternionAlgebra
noncomputable section

def dagger (q : B) : B := muInv * star q * mu

theorem trace_form (a b c d : ℤ) :
    4 * (dagger (embed (printed a b c d)) * embed (printed a b c d)).re =
      (((2*a+c)^2 + 6*(c-d)^2 + 2*(2*b+d)^2 + 3*(2*d-c)^2 : ℤ) : ℚ) := by
  rw [embed_printed]
  simp [dagger, muInv, mu]
  ring

theorem integral_minimum (a b c d : ℤ)
    (h : (2*a+c)^2 + 6*(c-d)^2 + 2*(2*b+d)^2 + 3*(2*d-c)^2 = 4) :
    (a = 1 ∨ a = -1) ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hA := sq_nonneg (2*a+c)
  have hB := sq_nonneg (2*b+d)
  have hD := sq_nonneg (2*d-c)
  have eq : c = d := by
    by_contra ne
    have pos := sq_pos_of_ne_zero (sub_ne_zero.mpr ne)
    omega
  subst d
  have lin : 2*c-c = c := by ring
  rw [sub_self,zero_pow (by decide : 2≠0),mul_zero,add_zero,lin] at h
  have small : c^2 ≤ 1 := by omega
  have range : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith only [small]
  have cz : c = 0 := by
    by_contra ne
    have nz : 2*b+c ≠ 0 := by omega
    have p := sq_pos_of_ne_zero nz
    have q := sq_pos_of_ne_zero ne
    omega
  subst c
  have ab : a^2+2*b^2=1 := by nlinarith only [h]
  have bz : b = 0 := by
    by_contra ne
    have pos := sq_pos_of_ne_zero ne
    have na := sq_nonneg a
    omega
  subst b
  have aa : a^2=(1:ℤ)^2 := by norm_num at ab ⊢; exact ab
  exact ⟨sq_eq_sq_iff_eq_or_eq_neg.mp aa,rfl,rfl,rfl⟩

theorem polarized_order_iff (x : O) :
    dagger (embed x) * embed x = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · obtain ⟨a,b,c,d,rfl⟩ := span_printed x
    intro h
    have real := congrArg QuaternionAlgebra.re h
    have h' := trace_form a b c d
    rw [real] at h'
    have integral : (2*a+c)^2 + 6*(c-d)^2 + 2*(2*b+d)^2 + 3*(2*d-c)^2 = 4 := by
      exact_mod_cast h'.symm
    obtain ⟨ha,rfl,rfl,rfl⟩ := integral_minimum a b c d integral
    rcases ha with rfl|rfl
    · left; ext <;> norm_num [printed]
    · right; ext <;> norm_num [printed]
  · rintro (rfl|rfl) <;> ext <;> norm_num [dagger,embed,mu,muInv]

end
end ZInQBlueprint.RosatiSigns
#print axioms ZInQBlueprint.RosatiSigns.trace_form
#print axioms ZInQBlueprint.RosatiSigns.integral_minimum
#print axioms ZInQBlueprint.RosatiSigns.polarized_order_iff
