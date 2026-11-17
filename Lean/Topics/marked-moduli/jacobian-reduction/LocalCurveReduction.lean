import ReductionPlaces
import WittQuadraticExtension
import SignedBranchRadicals
import OrdinaryReduction

/-! Local witnesses on the base change of the signed paper curve at every
prime outside the finite set in the effective height theorem. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.LocalCurveReduction
set_option maxHeartbeats 1500000
open BinaryCover ClusterPicture ClusterRoots DirectCharts PrimitiveParameters
open RationalReduction ResidueExtension GoodReductionCharts
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]
local notation "W" => IntegralField p
local notation "E" => WittVector p (WittSquareClasses.Extension p (QuadraticField p))

/-- The extension for the square roots is finite étale of rank four over Z_p.
The equality of maximal ideals and the common uniformizer are preserved at each step. -/
theorem radical_extension :
    letI : Algebra Zp E := ((WittSquareClasses.extend p (QuadraticField p)).comp (fromPadics p)).toAlgebra
    Module.Finite Zp E ∧ Algebra.Etale Zp E ∧ Module.finrank Zp E = 4 := by
  let : Algebra Zp E := ((WittSquareClasses.extend p (QuadraticField p)).comp (fromPadics p)).toAlgebra
  let : IsScalarTower Zp W E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := (finite_etale p).2
  let := (WittSquareClasses.finite_etale p (QuadraticField p)).1
  exact ⟨Module.Finite.trans W E, Algebra.Etale.comp Zp W E,
    by rw [← Module.finrank_mul_finrank Zp W E, integral_finrank,
      (WittSquareClasses.finite_etale p (QuadraticField p)).2]⟩

def OrdinaryFibre (u : ℚ) : Prop :=
  ∃ M : Over (Spec (.of Zp)), Smooth M.hom ∧ IsProper M.hom ∧ GeometricallyIntegral M.hom ∧
    Nonempty (paperPullback Qp u ≅ (Over.pullback (scalarMap Zp Qp)).obj M)

/-- A ramified-looking equation can have a singular curve fibre and still give
unramified radicals for Zarhin's quintic. The curve isomorphism here is over Q_p. -/
def RadicalChart (u : ℚ) : Prop :=
  ∃ (t : Zp) (v a : Zpˣ), Coordinates p u t (v : Zp) (a : Zp) ∧
    ∃ degree_six : (polynomial p u v a t).natDegree = 6, (polynomial p u v a t).Separable ∧
    Nonempty (paperPullback Qp u ≅ sexticCompletion (polynomial p u v a t) degree_six) ∧
    ∃ depth : ℕ, 0 < depth ∧
    ∃ (roots : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^depth))
      (radical : Fin 5 → Fin 5 → E), ∀ i j,
    radical i j ^ 2 =
      WittSquareClasses.extend p (QuadraticField p)
        (SixContactFour.transformed p roots (equation p u v a t).leadingCoeff i -
         SixContactFour.transformed p roots (equation p u v a t).leadingCoeff j)

private theorem of_differences {u : ℚ} (hu : u ∉ ZInQ.contactSet) (h2 : 2 < p)
    {t : Zp} {v a : Zpˣ} (hc : Coordinates p u t (v : Zp) (a : Zp)) {m : ℕ} (hm : 0 < m)
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^m))
    (h : SixContactFour.chartDifferences p T (equation p u v a t).leadingCoeff) :
    RadicalChart p u := by
  let r := SixContactFour.transformed p T (equation p u v a t).leadingCoeff
  have sq (i j : Fin 5) : ∃ z : E, z^2 = WittSquareClasses.extend p (QuadraticField p) (r i - r j) := by
    by_cases e : i = j
    · exact ⟨0, by simp [e]⟩
    · obtain ⟨n, hn⟩ := h i j e
      exact WittSquareClasses.even_sqrt p (QuadraticField p) h2 hn
  choose z hz using sq
  obtain ⟨hd, hs⟩ := ddmm_sextic_regular hu v a t hc
  obtain ⟨_, _, e, _, _⟩ := ddmm_smooth_completion_iso hu v a t hc
  exact ⟨t, v, a, hc, hd, hs, ⟨e⟩, m, hm, T, z, hz⟩

/-- Every prime allowed in the good-reduction conclusion has either an
integral smooth proper curve or one of the explicit split quintic charts. -/
theorem outside_conductor {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hp : p ∉ HeightBudget.conductorPrimes ZInQ.Mult.S_mul u) :
    OrdinaryFibre p u ∨ RadicalChart p u := by
  obtain ⟨hp17, cases⟩ := ReductionPlaces.outside_conductor hu hp
  rcases cases with ⟨hf, hg⟩ | ⟨k, hk, hf, _⟩ | ⟨g, hg, _, hv⟩
  · obtain ⟨t, a, _, hsm, hpr, hi, e⟩ := OrdinaryModel.ordinary_curve_model p hu (by omega) hf hg
    exact Or.inl ⟨_, hsm, hpr, hi, e⟩
  · obtain ⟨t, v, a, hc, T, h⟩ := SixContactFour.even_contact_differences p u hp17 k hk hf
    exact Or.inr (of_differences p hu (by omega) hc hk T h)
  · obtain ⟨t, a, hc, T, h⟩ := SixContactFour.pole_differences p u hp17 g hg hv
    exact Or.inr (of_differences p hu (by omega) hc hg T h)

end
end ZInQBlueprint.LocalCurveReduction
#print axioms ZInQBlueprint.LocalCurveReduction.radical_extension
#print axioms ZInQBlueprint.LocalCurveReduction.OrdinaryFibre
#print axioms ZInQBlueprint.LocalCurveReduction.RadicalChart
#print axioms ZInQBlueprint.LocalCurveReduction.outside_conductor
