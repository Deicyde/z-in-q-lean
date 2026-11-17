import PeriodAbscissaProjection

namespace Sun28.Abscissa
open Sun28.SeededPartners Sun28.NormPartners Sun28.PairedClasses Sun28.GlobalSections
open Sun28.PeriodWindows Sun28.QualitativeRows ZInQ
open ZInQBlueprint.FiveMetric ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods ZInQBlueprint.IntegralSections
noncomputable section

/-- An affine model of the isogeny covering for the abscissa squareclass b. -/
def quartic (b s : ℕ) : Prop :=
  ∃ u v : ℚ, u≠0 ∧ v≠0 ∧ v^2=(b:ℚ)*(u^2-s)*(u^2+3*s)

/-- Division by b*u gives the forward map. Multiplication gives its inverse. -/
theorem strict_iff_quartic {b s : ℕ} (bp : 0 < b) :
    strictPoint b (b*s) ↔ quartic b s := by
  have bn : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  constructor
  · rintro ⟨u,y,un,yn,E⟩
    refine ⟨u,y/((b:ℚ)*u),un,div_ne_zero yn (mul_ne_zero bn un),?_⟩
    push_cast at E
    field_simp
    linear_combination E
  · rintro ⟨u,v,un,vn,E⟩
    refine ⟨u,(b:ℚ)*u*v,un,mul_ne_zero (mul_ne_zero bn un) vn,?_⟩
    push_cast
    linear_combination ((b:ℚ)*u)^2*E

/-- The point obligation in one equation. Only the multiplier and two rationals are quantified. -/
def QuarticCompanion : Prop :=
  ∀ b d : ℕ, Residual b d → ∃ q, Candidate b d q ∧ quartic b (q*d)

theorem quartic_companion_iff : QuarticCompanion ↔ DivisorCompanion := by
  rw [divisor_companion_iff]
  constructor
  · intro lift b d r
    obtain ⟨q,C,K⟩:=lift b d r
    exact ⟨q,C,by simpa only [Nat.mul_assoc] using (strict_iff_quartic r.1.1).mpr K⟩
  · intro lift b d r
    obtain ⟨q,C,P⟩:=lift b d r
    exact ⟨q,C,(strict_iff_quartic r.1.1).mp (by simpa only [Nat.mul_assoc] using P)⟩

set_option maxRecDepth 14000
set_option exponentiation.threshold 250
theorem one_sign_of_quartic_windows (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72)
    (windows : ∀ k, ∃ F : PeriodFrame (integerWindow realCurves k) 576,
      ∀ i, ¬(active F.orders (Nat.factorial 576) i true ∧ active F.orders (Nat.factorial 576) i false))
    (lift : QuarticCompanion) (x:ℚ) :
    (∃ v : Fin 28 → ℚ, Sun28.eval28 Sun28.MultiplierChoice.oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) :=
  one_sign_of_divisor_windows table fibres realCurves windows (quartic_companion_iff.mp lift) x

end
end Sun28.Abscissa
#print axioms Sun28.Abscissa.strict_iff_quartic
#print axioms Sun28.Abscissa.quartic_companion_iff
#print axioms Sun28.Abscissa.one_sign_of_quartic_windows
