import GuitartSurfaces
import PicardPrym
import PicardPeriods
import PicardSurfaceDimension

/-! A conditional definition of the ordinary integers in the rational field.
The geometric inputs are quantified over abelian varieties or over the
published Prym and sextic models. The choice of a common number field,
the application to every twisted Picard Jacobian, and the passage to one
polynomial are deductions. The height coefficient and the arity are existential. -/

open AlgebraicGeometry CategoryTheory
open ZInQ ZInQ.QualitativeHeight ZInQBlueprint.AbelianModel
open ZOverQ.Qualitative.PicardConjugation ZOverQ.Qualitative.Picard.Assembly
namespace ZOverQ.Qualitative.PicardConclusion
open GuitartApplication GuitartSurfaces PicardPolynomial
noncomputable section
open scoped IntermediateField
local instance (M : FiniteGaloisIntermediateField ℚ Qbar) : NumberField M := ⟨⟩

/-- Bounded-degree CM finiteness on the marked Picard line. The set
`splitValues` is defined using elliptic subgroups of the actual canonical
Jacobian. See Laga–Shnidman, Remark 2.12 and Lemmas 6.2 and 6.16. -/
def FiniteSplitValues : Prop :=
  {j : Qbar | j ∈ PicardCM.splitValues ∧ Module.finrank ℚ ℚ⟮j⟯ ≤ 2}.Finite

/-- All fibres of the family have a uniformly bounded isogeny to a rational
quaternionic variety outside one finite set of invariant-line parameters.
The field, exceptional set and bound are part of the conclusion. -/
theorem marked_isogenies
    (cm : FiniteSplitValues) (prym : PicardPrym.PublishedPrymEndomorphisms)
    (multi : MultiplicationTheorem) (multipliers : RationalMultipliers) (guitart : GeometricDescent)
    (tate : ∀ L, TateSplitting L) :
    ∃ (M : FiniteGaloisIntermediateField ℚ Qbar) (ψ : fixedField →ₐ[ℚ] M) (except : Finset ℚ),
      MarkedIsogenies ψ (Module.finrank ℚ M) except := by
  classical
  let L := PicardPrym.standardField
  let ψ := IntermediateField.inclusion PicardPrym.fixed_le
  obtain ⟨T,_,outside⟩ := PicardPrym.quaternion_outside_finite prym cm
  let except := T.image picardParameter
  have ends (t : ℚ) (ht : t ∉ contactSet) (away : picardParameter t ∉ except) :
      Nonempty (PicardPrym.QuaternionModel (surface L ψ t ht)) := by
    let d : ℚ := (PrimitiveTwist.twist (picardParameter t) : ℤ)
    have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (PrimitiveTwist.positive _).ne'
    have hT : t ∉ T := fun hit => away (Finset.mem_image_of_mem _ hit)
    exact outside t d ht hd hT
  have systems := systems_of_endomorphisms multi multipliers guitart L ψ except
    (fun t ht => PicardSurfaceDimension.baseChange_dimension_two ψ.toRingHom t ht) ends
  obtain ⟨M,incl,h⟩ := uniform_marked_isogenies L ψ except (tate L) (multi Qbar) systems
  exact ⟨M,(IntermediateField.inclusion incl).comp ψ,except,h⟩

/-- The stable absolute Faltings height and its comparison with the actual
canonical period of a smooth sextic can be used over every finite normal
field, including the common field selected by Tate's theorem. -/
def HeightComparisons (hF : GroupScheme ℚ → ℝ) : Prop :=
  ∀ M : FiniteGaloisIntermediateField ℚ Qbar,
    ∃ (F : GroupScheme M → ℝ) (η : M →+* ℂ),
      IsogenyHeight.StableHeight F ∧ IsogenyHeight.DegreeBound F (2 * Module.finrank ℚ M) ∧
      (∀ B : GroupScheme ℚ, IsAbelianScheme B → F ((baseChange (algebraMap ℚ M)).obj B) = hF B) ∧
      PicardPeriods.SexticPeriods η F

/-- An integer polynomial defines ℤ in ℚ from the indicated geometric,
height and rank results. Neither a uniform height bound for the Picard
family nor a family of marked isogenies is a premise. -/
theorem integer_polynomial_of_arithmetic_geometry
    (cm : FiniteSplitValues) (prym : PicardPrym.PublishedPrymEndomorphisms)
    (multi : MultiplicationTheorem) (multipliers : RationalMultipliers) (guitart : GeometricDescent)
    (tate : ∀ L, TateSplitting L)
    (hF : GroupScheme ℚ → ℝ) (heights : HeightComparisons hF) (vk : VonKanel hF)
    (ddmm : PicardGoodReduction.SplitSexticDDMM) (st : ∀ (p : ℕ) [Fact p.Prime], SerreTateAt p)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  obtain ⟨M,ψ,except,marked⟩ := marked_isogenies cm prym multi multipliers guitart tate
  obtain ⟨F,η,stable,degree,extension,periods⟩ := heights M
  exact PicardPeriods.integer_polynomial_of_sextic_periods M ψ η hF F vk ddmm st
    (Module.finrank ℚ M) stable degree extension except marked periods tian grossZagier

end
end ZOverQ.Qualitative.PicardConclusion

#print axioms ZOverQ.Qualitative.PicardConclusion.marked_isogenies
#print axioms ZOverQ.Qualitative.PicardConclusion.integer_polynomial_of_arithmetic_geometry
