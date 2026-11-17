import NumeratorHeight
import SunCertificate

namespace Sun28.Ordinary
open Height NumberField IsDedekindDomain
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- The literal roots of Sun's three nonzero square scales A₀,A₁,A₂. -/
def scaleRoot (C₀ C₁ : ℚ) : Fin 3 → ℚ := ![1,C₀,1+C₁^2]

/-- The three certificates, the pointwise five-mark estimate and Corollary 2.4
give the two ordinary estimates and the logarithmic numerator comparison. -/
theorem marked_certificate_heights {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β C₀ C₁ η : ℚ) (M : Finset ℚ) (S : Finset ℕ)
    {C c₁ c₂ : ℝ} (hC : 1≤C) (hc₁ : 0≤c₁) (hc₂ : 0≤c₂)
    (hh : h≠0) (hc : h-c≠0)
    (outside : ∀ p : ℕ, p.Prime → p ∉ S → 65<p ∧ ¬(p:ℤ) ∣ c ∧ ¬p ∣ separation ∧ ∀ μ ∈ M, padicValRat p μ=0)
    (localChart : ∀ (p : ℕ) [hp : Fact p.Prime], p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
        OrdinaryFormalChart p w)
    (guard : ∀ j, (scaleRoot C₀ C₁ j)^2*η ∉ marks ∧ (scaleRoot C₀ C₁ j)^2*η ≠ 3 ∧ scaleRoot C₀ C₁ j≠0)
    (accepted : ∀ j, let s := scaleRoot C₀ C₁ j; let t := s^2*η
      testTrace root σ c h n m β (s^2) t ≠ 0 ∧ polePredicate M (poleArgument root σ c h n m β (s^2) t))
    (five : ∀ j, let t := (scaleRoot C₀ C₁ j)^2*η
      logHeight₁ t ≤ C*(∏ p ∈ contactPrimes S t, (p:ℝ))^24)
    (scale : ∀ H : ℝ, 1≤H → (∀ j, logHeight₁ ((scaleRoot C₀ C₁ j)^2*η)≤H) →
      (indexSize n)^2≤c₁*H+c₂) :
    let D := ordinaryConstant C c₁ c₂
    let Δ : ℤ := lucas (n 1) (n 2) (n 3)
    (Δ≠0 → (indexSize n)^2≤D*(1+|(Δ:ℝ)|^(3/8:ℝ))) ∧
    (β≠(n 0:ℚ) → (indexSize n)^2≤D*(1+((β-n 0).num.natAbs:ℝ)^(3/2:ℝ))) ∧
    (β≠(n 0:ℚ) → Real.log (indexSize n)≤numeratorConstant D+3*logHeight₁ β) := by
  let s := scaleRoot C₀ C₁
  let t := fun j => (s j)^2*η
  have prod := three_marked_products root σ hs c h n m β s t M S hh hc outside localChart guard accepted
  obtain ⟨d,j⟩ := ordinary_height_bounds S t n β hC hc₁ hc₂ five scale prod
  refine ⟨d,j,fun nz => ordinary_log_height β (n 0) (one_le_indexSize n) (abs_first_le_indexSize n) ?_ nz (j nz)⟩
  unfold ordinaryConstant
  nlinarith [mul_nonneg hc₁ (by linarith : 0≤C)]

/-- The ordinary estimates have the constants required by the existing multiplier. -/
theorem cutoff_from_ordinary {D S B c hβ : ℝ} (dp : 1≤D) (sc : 0≤S) {Δ : ℤ}
    (hc : (Sun28.multiplier D (numeratorConstant D) S : ℝ) ≤ c) (hB : c-1≤B)
    (lucas_upper : |(Δ:ℝ)|≤10*B^4)
    (ordinary : Δ≠0 → B^2≤D*(1+|(Δ:ℝ)|^(3/8:ℝ)))
    (scalar : hβ≤S*Real.sqrt c) :
    Δ=0 ∧ numeratorConstant D+3*hβ<c-4 := by
  obtain ⟨_,_,first,second⟩ := Sun28.multiplier_spec (K:=numeratorConstant D) (zero_le_one.trans dp) sc
  constructor
  · by_contra nz
    apply first B (by linarith)
    apply (ordinary nz).trans
    exact mul_le_mul_of_nonneg_left (add_le_add_right
      (Real.rpow_le_rpow (abs_nonneg _) lucas_upper (by norm_num : (0:ℝ)≤3/8)) 1) (zero_le_one.trans dp)
  · linarith [second c hc]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.marked_certificate_heights
#print axioms Sun28.Ordinary.cutoff_from_ordinary
