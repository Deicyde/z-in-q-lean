import WitnessCoordinates
import ScalarOctic
import FieldProjection

/-! The two input loci required by the integer-only implication. -/
namespace Sun28.WitnessHeight
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.FixedPreparation
open Sun28.ScalarHeight Sun28.FiveDescent.ResidueField Sun28.FiveMarkUnits Height
noncomputable section

/-- At an ordinary slope the coordinate field comes from the transformed value 2+1/t. -/
theorem ordinary_coordinates (t : ℚ) (off : t∉marks) :
    let q := 1-t/(2*t+1)
    ∃ z v : Omega, z≠0 ∧ v≠0 ∧ z^2=algebraMap ℚ Omega q ∧
      v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) ∧ fieldPrimes z v=contactPrimes oldCutoff t := by
  let s := sourcePair t
  have row := exists_coordinates (source_primitive t) (source_off t off)
  obtain ⟨z,v,nz,nv,zq,curve,_,sets,_⟩ := row
  have tf : (t.num:ℚ)=t*t.den := (div_eq_iff (by exact_mod_cast t.den_nz)).mp t.num_div_den
  have dn : (t.den:ℚ)≠0 := by exact_mod_cast t.den_nz
  have frac : ((sourcePair t).2:ℚ)/(sourcePair t).1=t/(2*t+1) := by
    simp only [sourcePair,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,tf]
    rw [show 2*(t*(t.den:ℚ))+t.den=(2*t+1)*t.den by ring,mul_div_mul_right _ _ dn]
  refine ⟨z,v,nz,nv,?_,curve,?_⟩
  · simpa only [frac] using zq
  · change fieldPrimes z v=oldContactPrimes oldCutoff (2*t.num+t.den) t.num at sets
    exact sets.trans (transported_contact_primes oldCutoff t)

private theorem fieldPrimes_sign {z w v u : Omega} (hz : z^2=w^2) (hv : v^2=u^2) :
    fieldPrimes z v=fieldPrimes w u := by
  have choice {a b:Omega} (eq : a^2=b^2) : ∃ k:ℚ,k≠0 ∧ a=b*algebraMap ℚ Omega k := by
    have h:(a-b)*(a+b)=0 := by linear_combination eq
    rcases mul_eq_zero.mp h with pos|neg
    · exact ⟨1,one_ne_zero,by simpa using sub_eq_zero.mp pos⟩
    · exact ⟨-1,by decide,by simpa using eq_neg_of_add_eq_zero_left neg⟩
  obtain ⟨k,nk,ek⟩:=choice hz
  obtain ⟨l,nl,el⟩:=choice hv
  have same : coords z v=coords w u := by
    rw [ek,el]
    exact generated_coordinates w u nk nl
  unfold fieldPrimes
  rw [NumberField.discr_eq_discr_of_algEquiv _ (IntermediateField.equivOfEq same)]

theorem ordinary_field_primes (t : ℚ) (off : t∉marks) (z v : Omega)
    (hz : z^2=algebraMap ℚ Omega (1-t/(2*t+1)))
    (hv : v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2)) :
    fieldPrimes z v=contactPrimes oldCutoff t := by
  obtain ⟨w,u,_,_,hw,hu,e⟩ := ordinary_coordinates t off
  exact (fieldPrimes_sign (hz.trans hw.symm) (by rw [hv,hu,hz,hw])).trans e

def ordinaryFieldUnion (z v : Fin 3 → Omega) : Finset ℕ :=
  Finset.univ.biUnion fun i => fieldPrimes (z i) (v i)

/-- The two curve estimates have no elliptic, Pell, or prime-counting input.
Both are asked at actual decoded rational tuples; all radicals retain the original cutoff. -/
structure TwoLocusHeight : Prop where
  scalar : ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24
  ordinary : ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    let t := slope (nineAffine A).doubles η
    ∀ z v : Fin 3 → Omega,
      (∀ i,z i≠0 ∧ v i≠0 ∧ (z i)^2=algebraMap ℚ Omega (1-t i/(2*t i+1)) ∧
        (v i)^2=(1-(z i)^2)*(2401*(z i)^2-2400)*(375-343*(z i)^2)) →
      ∃ j, (∀ i,logHeight₁ (t i)≤logHeight₁ (t j)) ∧
        logHeight₁ (t j)≤fiveHeightConstant oldCutoff*(primeProduct (ordinaryFieldUnion z v):ℝ)^24

theorem two_loci_of_uniform (bound : OriginalFiveHeight glazerConstant24 oldCutoff) : TwoLocusHeight := by
  constructor
  · intro _ x _ _ _
    exact (scalar_target_iff x).mp (bound _ _ (beta_primitive x) (beta_off_forms x))
  · intro A _ η _ accepted
    dsimp only
    intro z v coord
    let t:=slope (nineAffine A).doubles η
    have sets (i:Fin 3) := ordinary_field_primes (t i) (accepted.scale_guard i).1 (z i) (v i)
      (coord i).2.2.1 (coord i).2.2.2
    have same : ordinaryFieldUnion z v=contactUnion oldCutoff t := by
      unfold ordinaryFieldUnion contactUnion
      simp only [sets]
    obtain ⟨j,mx⟩:=maximum_exists t
    refine ⟨j,mx,?_⟩
    rw [same]
    exact ordinary_to_union t j (bound _ _ (source_primitive _) (source_off _ (accepted.scale_guard j).1))

/-- A single square root suffices for the scalar discriminant. -/
theorem scalar_field_primes (x:ℚ) (r:Omega) (hr:r^2=(scalarClass x:Omega)) :
    fieldPrimes r 1=scalarPrimes x := by
  have one : Squarefree (1:ℤ) := squarefree_one
  have e:=fieldPrimes_eq (octic_twist x).1 one hr (w:=1) (by norm_num)
  simpa only [FiveDescent.twistPrimes,FiveDescent.parameterPrimes,scalarPrimes,Int.natAbs_one,
    Nat.primeFactors_one,Finset.union_empty] using e

/-- Every hypothetical nonintegral zero furnishes a rational point on the scalar
twist and three lifts on the fixed sextic. The displayed two inequalities exclude it. -/
theorem integral_of_two_loci (height : TwoLocusHeight) (x : ℚ)
    (zero : ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) : ∃ z : ℤ, x=(z:ℚ) := by
  classical
  by_contra nonintegral
  obtain ⟨A,η,accepted⟩ := (Concrete.polynomial_iff_certificate _).1 zero
  let t := slope (nineAffine A).doubles η
  have lift := fun i => ordinary_coordinates (t i) (accepted.scale_guard i).1
  choose z v nz nv zq curve sets using lift
  obtain ⟨j,mx,h⟩ := height.ordinary A x η nonintegral accepted z v (fun i=>⟨nz i,nv i,zq i,curve i⟩)
  have same : ordinaryFieldUnion z v=contactUnion oldCutoff t := by
    unfold ordinaryFieldUnion contactUnion
    simp only [sets]
  rw [same] at h
  exact nonintegral (integral_of_union_height A x η accepted j mx h
    ((scalar_target_iff x).mpr (height.scalar A x η nonintegral accepted)))

theorem two_loci_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (height : TwoLocusHeight)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  refine ⟨integral_of_two_loci height x,?_⟩
  rintro ⟨k,rfl⟩
  exact fibre_of_integer realCurves quadric moments (GlobalDescent.sections_iff_descent.mpr points) k

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.ordinary_coordinates
#print axioms Sun28.WitnessHeight.integral_of_two_loci
#print axioms Sun28.WitnessHeight.two_loci_projection
#print axioms Sun28.WitnessHeight.ordinary_field_primes
#print axioms Sun28.WitnessHeight.two_loci_of_uniform
#print axioms Sun28.WitnessHeight.scalar_field_primes
