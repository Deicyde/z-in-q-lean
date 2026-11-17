import ActualCutoff
import HeightTransport

namespace Sun28.Ordinary
open Height NumberField IsDedekindDomain
open scoped NumberField

theorem logHeight_reduced_pair (t : ℚ) : logHeight₁ t=pairLogHeight t.num t.den := by
  rw [Rat.logHeight₁_eq_log_max]
  unfold pairLogHeight pairHeight
  congr 1
  norm_cast
  simp

/-- A single numerical coefficient with cutoff enlargement and the normalization C≥1. -/
noncomputable def fiveHeightConstant (S : Finset ℕ) : ℝ :=
  max 1 (glazerConstant24*(∏ p ∈ extraPrimes oldCutoff S,(p:ℝ))^24+Real.log 3)

theorem upstream_three_heights (S : Finset ℕ)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff)
    (t : Fin 3 → ℚ) (off : ∀ j, t j∉marks) :
    ∀ j, logHeight₁ (t j)≤fiveHeightConstant S*(∏ p ∈ contactPrimes S (t j),(p:ℝ))^24 := by
  intro j
  rw [logHeight_reduced_pair]
  have bound := glazer_five_height_transported S upstream (t j) (off j)
  simp only [contactRadical,Nat.cast_prod] at bound
  apply bound.trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The local certificates imply both ordinary soundness inequalities with
Glazer's original five-mark statement as the sole five-contact height input. -/
theorem marked_heights_from_glazer {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    [Algebra.IsQuadraticExtension ℚ K] {ρ : K} (root : ρ^2=2)
    (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β C₀ C₁ η : ℚ) (M : Finset ℚ) (S : Finset ℕ)
    {c₁ c₂ : ℝ} (hc₁ : 0≤c₁) (hc₂ : 0≤c₂)
    (hh : h≠0) (hc : h-c≠0)
    (outside : ∀ p : ℕ, p.Prime → p ∉ S → 65<p ∧ ¬(p:ℤ) ∣ c ∧ ¬p ∣ separation ∧ ∀ μ ∈ M, padicValRat p μ=0)
    (localChart : ∀ (p : ℕ) [hp : Fact p.Prime], p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
        OrdinaryFormalChart p w)
    (guard : ∀ j, (scaleRoot C₀ C₁ j)^2*η ∉ marks ∧ (scaleRoot C₀ C₁ j)^2*η ≠ 3 ∧ scaleRoot C₀ C₁ j≠0)
    (accepted : ∀ j, let s := scaleRoot C₀ C₁ j; let t := s^2*η
      testTrace root σ c h n m β (s^2) t ≠ 0 ∧ polePredicate M (poleArgument root σ c h n m β (s^2) t))
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff)
    (scale : ∀ H : ℝ, 1≤H → (∀ j, logHeight₁ ((scaleRoot C₀ C₁ j)^2*η)≤H) →
      (indexSize n)^2≤c₁*H+c₂) :
    let D := ordinaryConstant (fiveHeightConstant S) c₁ c₂
    let Δ : ℤ := lucas (n 1) (n 2) (n 3)
    (Δ≠0 → (indexSize n)^2≤D*(1+|(Δ:ℝ)|^(3/8:ℝ))) ∧
    (β≠(n 0:ℚ) → (indexSize n)^2≤D*(1+((β-n 0).num.natAbs:ℝ)^(3/2:ℝ))) ∧
    (β≠(n 0:ℚ) → Real.log (indexSize n)≤numeratorConstant D+3*logHeight₁ β) := by
  have three := upstream_three_heights S upstream (fun j => (scaleRoot C₀ C₁ j)^2*η)
    (fun j => (guard j).1)
  exact marked_certificate_heights root σ hs c h n m β C₀ C₁ η M S
    (C:=fiveHeightConstant S) (le_max_left _ _) hc₁ hc₂ hh hc outside localChart guard accepted three scale

end Sun28.Ordinary
#print axioms Sun28.Ordinary.logHeight_reduced_pair
#print axioms Sun28.Ordinary.upstream_three_heights
#print axioms Sun28.Ordinary.marked_heights_from_glazer
