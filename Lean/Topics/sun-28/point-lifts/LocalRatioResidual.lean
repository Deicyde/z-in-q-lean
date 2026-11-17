import RatioPrimes

namespace Sun28.PointLifts
open Sun28.PairedClasses Sun28.PointFibres Sun28.PointDescent Sun28.PrescribedPoints
  Sun28.PreparedPoles Sun28.TwistRank Sun28.TwistExtension ZInQ.RouteK
noncomputable section

/-- Local restrictions on the *physical* square root of the marked abscissa ratio. -/
def AllowedRatio (b θ : ℕ) (s : ℚ) : Prop :=
  s≠0 ∧ (∀ p : ℕ, p.Prime → AnisotropicPrime b p → padicValRat p s=0) ∧
    (∀ (p : ℕ) (hp : p.Prime), p∣b → (3:ZMod p)≠0 → @RamifiedRay p θ ⟨hp⟩ s)

theorem allowed_of_fibre {b θ : ℕ} {s : ℚ} (a : AdmissiblePair b θ)
    (sn : s≠0) (H : SingleFibre b θ s) : AllowedRatio b θ s := by
  obtain ⟨z,h,j,F⟩:=(conics_iff_single (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne') sn).mpr H
  refine ⟨sn,?_,?_⟩
  · intro p hp bad;let _ : Fact p.Prime:=⟨hp⟩
    exact admissible_ratio_unit a bad F
  · intro p hp pb p3;let _ : Fact p.Prime:=⟨hp⟩
    exact ratio_ramified_ray a pb p3 F

theorem surface_iff_local_ratios {b θ : ℕ} (a : AdmissiblePair b θ) :
    Surface b θ ↔ ∃ s : ℚ, AllowedRatio b θ s ∧ SingleFibre b θ s := by
  rw [surface_iff_single (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne')]
  exact ⟨fun ⟨s,sn,H⟩=>⟨s,allowed_of_fibre a sn H,H⟩,
    fun ⟨s,r,H⟩=>⟨s,r.1,H⟩⟩

/-- Remaining assertion on the same prepared inputs after the known sections.
The conclusion requires a rational point on an explicitly given binary quartic. -/
def LocalRatioResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) →
  ∃ s : ℚ, AllowedRatio b θ s ∧ SingleFibre (b:ℚ) (θ:ℚ) s

theorem pencil_residual_iff_local_ratios : PencilResidual ↔ LocalRatioResidual := by
  constructor
  · intro H b θ a input fixed norm fac one out
    apply (surface_iff_local_ratios a).mp
    apply (surface_iff_one_or_nonzero (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne')).mpr
    exact Or.inr (H b θ a input fixed norm fac one out)
  · intro H b θ a input fixed norm fac one out
    have F:=(surface_iff_local_ratios a).mpr (H b θ a input fixed norm fac one out)
    exact ((surface_iff_one_or_nonzero (by exact_mod_cast a.1) (by exact_mod_cast a.2.1.ne')).mp F).resolve_left one

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.allowed_of_fibre
#print axioms Sun28.PointLifts.surface_iff_local_ratios
#print axioms Sun28.PointLifts.pencil_residual_iff_local_ratios
