import AlgebraicThetaPeriod
import Mathlib.Analysis.Complex.Exponential

/-! The analytic hypotheses expressed using the literal genus-two theta series
of a single symmetric period matrix in the Siegel upper half space. -/
namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient SexticThetaHeight SexticInvariants
noncomputable section

/-- A symmetric 2×2 period with positive-definite imaginary part. The two
inequalities are Sylvester's criterion for its first and second leading minors. -/
structure SiegelPeriod where
  z11 : ℂ
  z12 : ℂ
  z22 : ℂ
  im11 : 0 < z11.im
  imdet : 0 < z11.im*z22.im-z12.im^2

/-- The Streng/Dupont indexing j=16c₂+8c₁+4c₄+2c₃ puts c′ in the high bits.
The eigencharacteristic parity is symmetric in c′ and c″. -/
def halfBit (j : Fin 16) (k : ℕ) : ℂ := ((j.val / 2^k % 2 : ℕ):ℂ)/2

def term (Z : SiegelPeriod) (j : Fin 16) (n : ℤ × ℤ) : ℂ :=
  let p := (n.1:ℂ) + halfBit j 2
  let q := (n.2:ℂ) + halfBit j 3
  Complex.exp (2*Real.pi*Complex.I * ((p^2*Z.z11 + 2*p*q*Z.z12 + q^2*Z.z22)/2 +
    p*halfBit j 0 + q*halfBit j 1))

def thetaNull (Z : SiegelPeriod) : Tuple := fun j => ∑' n : ℤ × ℤ, term Z j n

/-- The genus-two period and normalized Faltings height can come from the same
polarized Jacobian. Constructing them and identifying that Jacobian constitute
the geometric obligations in an application. -/
structure SiegelPeriodData (u δ : ℚ) where
  matrix : SiegelPeriod
  algebraic : ∀ i, IsAlgebraic ℚ (chart (thetaNull matrix) i)
  evenProduct : pct (thetaNull matrix) ≠ 0
  streng : absInvariant (thetaNull matrix) =
    ((igusaI4 (sextic u δ)^5/(sextic u δ).discr^2 : ℚ) : ℂ)
  stable : ℝ
  comparison : |max 1 (chartHeight (thetaNull matrix) algebraic) -
      max 1 (stable + Real.log Real.pi)/2| ≤ ThetaMetric.pazukiConstant *
      Real.log (min (max 1 (chartHeight (thetaNull matrix) algebraic))
        (max 1 (stable + Real.log Real.pi)) + 2)
  reduction : stable ≤ HeightBudget.vonKaenelBudget u

def toAnalytic {u δ : ℚ} (p : SiegelPeriodData u δ) : AnalyticPeriodData u δ where
  null := thetaNull p.matrix
  algebraic := p.algebraic
  evenProduct := p.evenProduct
  period := p.streng
  stable := p.stable
  comparison := p.comparison
  reduction := p.reduction

def HasSiegelPeriods : Prop := ∀ u : ℚ, u ∉ ZInQ.contactSet →
  ∃ δ : ℚ, δ ≠ 0 ∧ Nonempty (SiegelPeriodData u δ)

theorem sexticPeriods_of_siegelPeriods (h : HasSiegelPeriods) : HasSexticPeriods := by
  apply sexticPeriods_of_analyticPeriods
  intro u hu
  obtain ⟨δ,hδ,⟨p⟩⟩ := h u hu
  exact ⟨δ,hδ,⟨toAnalytic p⟩⟩

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.toAnalytic
#print axioms ZInQBlueprint.ThetaPeriod.sexticPeriods_of_siegelPeriods
