import MarkedLevelEndpoint
import PreparedWitnessChoice
import HilbertArtin

/-! The original finite-torsion bound using actual number-field ramification groups.
The sharper quaternionic route and the multiplier-choice forward proof meet at the
same literal polynomial. -/
namespace ZInQBlueprint.WildLevel
open NumberField Finset ZInQBlueprint.FiveMetric
open scoped NumberField
open ZInQKernel.Contrib.HilbertDifferent
open Sun28.SurfaceHeight.HilbertArtin
noncomputable section

/-- Only positive ramification groups must be detected in F′. All tame
contributions of the full ℓ-adic representation are kept in t. -/
theorem conductor_on_fibre_field (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p:ℤ)})]
    (n t a : ℕ) (c : ℕ → ℕ) (tame : t≤2) (dimension : ∀ j,c j≤2)
    (detects : ∀ j,ramGroup L P (j+1)=⊥ → c j=0)
    (artin : P.ramificationIdx ℤ*a=P.ramificationIdx ℤ*t+∑ j∈range n,ramCard L P (j+1)*c j) :
    a≤2+4*padicValNat p (P.ramificationIdx ℤ) := by
  let e := P.ramificationIdx ℤ
  have he : 0<e:=Ideal.ramificationIdx_pos ℤ P
  have sw:=weighted_wild_le L p P 2 n c detects dimension
  apply Nat.le_of_mul_le_mul_left (c:=e) _ he
  calc e*a = e*t+∑ j∈range n,ramCard L P (j+1)*c j := artin
       _ ≤ e*2+2*2*(e*padicValNat p e) := Nat.add_le_add (Nat.mul_le_mul_left e tame) sw
       _ = e*(2+4*padicValNat p e) := by ring

/-- Both directions retain the same x and the same list of 28 witnesses.
The real and quadric facts and the prime input enter only in the forward direction. -/
theorem polynomial_of_multiplier_choice (realCurves : Sun28.RealComponents.PublishedProposition72)
    (quadric : Sun28.ConeCount.PublishedQuadricCount) (input : LevelApplications)
    (moments : Sun28.PrimeValues.FirstMomentInputs) (choice : Sun28.MultiplierChoice.ChoiceResidual)
    (x : ℚ) : (∃ w : Fin 28 → ℚ,Sun28.eval28 Sun28.Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  refine ⟨Sun28.WitnessHeight.integral_of_two_loci
    (Sun28.WitnessHeight.two_loci_of_uniform (five_height_of_surface (surface_of_level input))) x,?_⟩
  rintro ⟨k,rfl⟩
  exact Sun28.MultiplierChoice.integer_root realCurves (Sun28.PrimeValues.surplus_of_moments moments
    (Sun28.ConeSieve.row_of_congruences (Sun28.ConeCount.upper_sieve quadric))) choice k

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.conductor_on_fibre_field
#print axioms ZInQBlueprint.WildLevel.polynomial_of_multiplier_choice
