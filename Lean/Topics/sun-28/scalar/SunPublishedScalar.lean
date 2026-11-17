import SunTraceIndex
import Mathlib.GroupTheory.OrderOfElement

/-! Identification with the literal coordinates in Sun's fixed cyclic carrier. -/
namespace Sun28.Scalar
open WeierstrassCurve.Affine Sun28.ScalarTrace
noncomputable section
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def generatorX (ρ : K) : K := 57/8-7/2*ρ
def generatorY (ρ : K) : K := -165/8+417/32*ρ

omit [DecidableEq K] in
theorem generator_on_curve {ρ : K} (root : ρ^2=2) :
    (curve (-(3-ρ)^2)).Nonsingular (generatorX ρ) (generatorY ρ) := by
  rw [nonsingular_iff']
  constructor
  · rw [equation_iff]
    simp [curve,generatorX,generatorY]
    ring_nf
    simp [root,show ρ^3=2*ρ by rw [pow_succ,root]]
    ring
  · right
    simp [curve,generatorX,generatorY]
    intro h
    have he : ρ=220/139 := by linear_combination (norm := ring_nf) (32/417)*h
    rw [he] at root
    norm_num at root

def paperGenerator {ρ : K} (root : ρ^2=2) : (curve (-(3-ρ)^2)).Point :=
  Point.some _ _ (generator_on_curve root)

variable [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]

/-- The contact implication for the fixed displayed generator, with the paper's
infinite-order theorem and the local formal-comparison lemma as explicit inputs. -/
theorem published_scalar48 {p : ℕ} [Fact p.Prime] (hp : 2<p)
    (w : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[ℚ] K) (hσ : σ≠1)
    {ρ : K} (root : ρ^2=2) (h2 : w (2:K)=0)
    (infinite : addOrderOf (paperGenerator root)=0)
    (comp₁ : FormalComparison p w (paperGenerator root))
    (comp₂ : FormalComparison p (w.comap σ.toRingHom) (paperGenerator root))
    {h s : ℤ} (hh : h≠0) {r Γ D₀ : ℚ} {α : ℤ}
    (hr : w (algebraMap ℚ K r)=(α:WithTop ℤ)) (ho : Odd α)
    (front : w (algebraMap ℚ K (Γ/(1+D₀*r^2)))=0)
    (nonzero : scalarTheta r (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root))≠0)
    (pole : 0 ≤ w (algebraMap ℚ K (scalarValue r Γ D₀ (reciprocal (h • paperGenerator root))
      (parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root))))) :
    (p:ℤ)^48 ∣ s-1 := by
  apply trace_scalar48 hp w σ hσ root h2 (paperGenerator root) _ comp₁ comp₂ hh hr ho front nonzero pole
  intro j hj hz
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  rw [infinite] at hd
  simp [hj] at hd

#print axioms generator_on_curve
#print axioms published_scalar48
end
end Sun28.Scalar
