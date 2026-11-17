import NegativeCircle
import Mathlib.Data.Rat.Sqrt

namespace Sun28.ConicNegative
noncomputable section

def Q₀ {R : Type*} [CommRing R] (a b : R) : R :=
  17460*a^4+8820*a^3*b-5695*a^2*b^2-1470*a*b^3+485*b^4
def Q₁ {R : Type*} [CommRing R] (a b : R) : R :=
  26460*a^4+12348*a^3*b-7301*a^2*b^2-2058*a*b^3+735*b^4
def Q₂ {R : Type*} [CommRing R] (a b : R) : R :=
  199332*a^4+98784*a^3*b-62524*a^2*b^2-16464*a*b^3+5537*b^4

def rationalFactors (s : ℚ) : Prop :=
  IsSquare s ∧ IsSquare (35*(s+8/5)) ∧ IsSquare (70*(s+3/8))

theorem projective_chart {s:ℚ} (h:component s) :
    ∃ a b:ℤ, 0<b ∧ a.natAbs.Coprime b.natAbs ∧
      120*s*((b:ℚ)^2+6*(a:ℚ)^2)^2=H a b := by
  obtain ⟨t,e⟩:=component_chart h
  have bn : (t.den:ℚ)≠0:=by exact_mod_cast t.den_nz
  have er : (t.num:ℚ)=t*t.den := (div_eq_iff bn).mp t.num_div_den
  refine ⟨t.num,t.den,by exact_mod_cast t.den_pos,by simpa using t.reduced,?_⟩
  push_cast
  rw [er]
  dsimp [H] at e ⊢
  linear_combination (t.den:ℚ)^4*e

/-- The three rational root components and the fourth quadratic component lead to
simultaneous integral quartic squares at a primitive projective pair. -/
theorem integral_quartics {s:ℚ} (h:component s) (f:rationalFactors s) :
    ∃ a b:ℤ, 0<b ∧ a.natAbs.Coprime b.natAbs ∧
      120*s*((b:ℚ)^2+6*(a:ℚ)^2)^2=H a b ∧
      IsSquare (Q₀ a b) ∧ IsSquare (Q₁ a b) ∧ IsSquare (Q₂ a b) := by
  obtain ⟨a,b,bp,cop,e⟩:=projective_chart h
  obtain ⟨⟨u,eu⟩,⟨v,ev⟩,⟨w,ew⟩⟩:=f
  let D:ℚ:=(b:ℚ)^2+6*(a:ℚ)^2
  change 120*s*D^2=H a b at e
  refine ⟨a,b,bp,cop,e,?_,?_,?_⟩
  · apply Rat.isSquare_intCast_iff.mp
    refine ⟨5*D*u,?_⟩
    simp only [Q₀,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_sub,Int.cast_ofNat]
    dsimp only [H] at e
    dsimp only [D] at *
    linear_combination -(25/120:ℚ)*e + 25*((b:ℚ)^2+6*(a:ℚ)^2)^2*eu
  · apply Rat.isSquare_intCast_iff.mp
    refine ⟨D*v,?_⟩
    simp only [Q₁,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_sub,Int.cast_ofNat]
    dsimp only [H] at e
    dsimp only [D] at *
    linear_combination -(35/120:ℚ)*e + ((b:ℚ)^2+6*(a:ℚ)^2)^2*ev
  · apply Rat.isSquare_intCast_iff.mp
    refine ⟨2*D*w,?_⟩
    simp only [Q₂,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_sub,Int.cast_ofNat]
    dsimp only [H] at e
    dsimp only [D] at *
    linear_combination -(280/120:ℚ)*e + 4*((b:ℚ)^2+6*(a:ℚ)^2)^2*ew

end
end Sun28.ConicNegative
#print axioms Sun28.ConicNegative.projective_chart
#print axioms Sun28.ConicNegative.integral_quartics
