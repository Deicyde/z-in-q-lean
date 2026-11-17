import ZInQ.PoleValuation
import Mathlib.Tactic

/-! The soundness half of Sun's two-structural-parameter pole predicate. -/
open ZInQ.ValuationObstruction
namespace Sun28.Ordinary

def poleBranch (μ B e z : ℚ) : Prop :=
  let A := μ*B
  let H := A*(A-B^2)
  A*e*H*z ≠ 0 ∧ ∃ y₁ y₂ : ℚ,
    y₁^2=A*(A-e)*(A+3*e) ∧
    y₂^2=A*(A*z^2-e*H)*(A*z^2+3*e*H)

def polePredicate (M : Finset ℚ) (B : ℚ) : Prop :=
  B=0 ∨ ∃ μ ∈ M, ∃ e z, poleBranch μ B e z

theorem poleBranch_sound {p : ℕ} [hp : Fact p.Prime] (large : 3<p)
    {μ B e z : ℚ} (unit : padicValRat p μ=0) (branch : poleBranch μ B e z)
    (odd : Odd (padicValRat p B)) : 0 ≤ padicValRat p B := by
  let A:=μ*B
  let H:=A*(A-B^2)
  obtain ⟨guard,y₁,y₂,first,second⟩ := branch
  change A*e*H*z≠0 at guard
  change y₁^2=A*(A-e)*(A+3*e) at first
  change y₂^2=A*(A*z^2-e*H)*(A*z^2+3*e*H) at second
  obtain ⟨g,z0⟩ := mul_ne_zero_iff.mp guard
  obtain ⟨g,H0⟩ := mul_ne_zero_iff.mp g
  obtain ⟨A0,e0⟩ := mul_ne_zero_iff.mp g
  obtain ⟨μ0,B0⟩ := mul_ne_zero_iff.mp A0
  have av : padicValRat p A=padicValRat p B := by
    rw [show A=μ*B from rfl,padicValRat.mul μ0 B0,unit,zero_add]
  by_contra! neg
  have hv : padicValRat p H=3*padicValRat p B :=
    (negative_input_pole_h_valuation p hp.out μ B μ0 B0 unit neg).2.2
  obtain ⟨k,hk⟩ := odd
  rcases Int.even_or_odd (padicValRat p e) with he|⟨j,hj⟩
  · obtain ⟨j,hj⟩ := elliptic_x_valuation_even_of_parameter_even p hp.out (by omega) (by omega)
      A e y₁ A0 e0 he first
    omega
  · have even : Even (padicValRat p (e*H)) := by
      rw [padicValRat.mul e0 H0,hv]
      exact ⟨j+3*k+2,by omega⟩
    have sq : (z*y₂)^2=(A*z^2)*((A*z^2)-(e*H))*((A*z^2)+3*(e*H)) := by
      rw [mul_pow,second]
      ring
    have nz := pow_ne_zero 2 z0
    obtain ⟨l,hl⟩ := elliptic_x_valuation_even_of_parameter_even p hp.out (by omega) (by omega)
      (A*z^2) (e*H) (z*y₂) (mul_ne_zero A0 nz) (mul_ne_zero e0 H0) even sq
    rw [padicValRat.mul A0 nz,padicValRat.pow,av] at hl
    omega

theorem polePredicate_sound {p : ℕ} [Fact p.Prime] (large : 3<p) (M : Finset ℚ) {B : ℚ}
    (outside : ∀ μ ∈ M, padicValRat p μ=0) (pole : polePredicate M B)
    (odd : Odd (padicValRat p B)) : 0 ≤ padicValRat p B := by
  rcases pole with rfl|⟨μ,mem,e,z,h⟩
  · simp
  · exact poleBranch_sound large (outside μ mem) h odd

end Sun28.Ordinary
#print axioms Sun28.Ordinary.poleBranch_sound
#print axioms Sun28.Ordinary.polePredicate_sound
