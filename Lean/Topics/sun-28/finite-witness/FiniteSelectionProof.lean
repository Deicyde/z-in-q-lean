import SieveOrders
import ContactBounds
import ScalarPreparation
import SelectedTraceCRT
import CMPointCounts
import JointPreparation

/-! Every finite-place and index requirement in the 28-witness polynomial
is supplied by one simultaneous Gaussian-prime tuple. -/
namespace Sun28.FiniteWitness
open IsDedekindDomain NumberField
open scoped NumberField
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.WitnessIndices Sun28.ContactFactors Sun28.ScalarPlaces
open Sun28.GaussianSelection Sun28.Exceptional Sun28.SelectedTrace Sun28.RealRatio
open ManuscriptV15.Arithmetic
noncomputable section

/-- Integrality of the ordinary expressions at the two conjugate places. -/
def IntegralTests : Prop :=
  ∀ p : ℕ, ∀ prime : p.Prime, p∈primes → ∀ place : HeightOneSpectrum (𝓞 K0),
    place.asIdeal.LiesOver (basePrime p prime).asIdeal → ∀ (w : NinePoints) (M : ℕ) (q h β : ℤ) (n : Fin 4→ℤ),
    Consequences w M anchor ⟨q,h,n,fun i=>h*n i⟩ → anchor∣h →
    IntegralAtBoth place (ordinaryAt w M anchor (β:ℚ))

/-- The early modulus depends on the integer input. Prime selection may depend
on the four roots and on the real bound, and every later CRT index works. -/
theorem selection_of_integral_tests (sieve : ContactSieve.PrimePatterns) (integral : IntegralTests) : FiniteSelection := by
  classical
  intro X
  let r:=integerRadicand X
  let T:=supportPlaces r
  let κ:=kernelMod r
  let a:=comparisonDepth r
  let M:=fixedMultiplier
  have mp : 0<M := by have := fixed_multiplier_spec.2.1; change 0<fixedMultiplier; omega
  obtain ⟨dp,mdiv,_⟩ := step_spec r mp
  refine ⟨stepMod r M,0,dp,mdiv,?_⟩
  intro c q n C dc cl cq first shift odds luc _one
  let A:=fixedScale n
  have unitScale : A 0=1 := by norm_num [A,fixedScale,scaleRoot]
  have alive : ∀ j,A j≠0 := fun j => (actual_scales_positive n (fun i=>(odds i).1.ne') j).ne'
  have two : 2∈T := Finset.mem_union_left _ (by decide : 2∈primes)
  obtain ⟨u,v,values,π,o,_,vp,dv,large,ahead,exclude,oriented,lp,lm,ko,ts,ao⟩ :=
    ContactSieve.select_with_orders sieve (X:=X) (c:=c) (q:=q) (n:=n)
      ⟨by omega,cq,first,shift,odds,luc⟩ (requiredDivisor A) κ T a (divisor_positive A)
      (kernel_positive r) (fun _ => support_prime) two (fun _ _ => by dsimp [κ,a,comparisonDepth]; omega)
      (by dsimp [a,comparisonDepth]; omega) (slopeThreshold A C (1/2)) (selectionBound T)
  refine ⟨u,v,values,o,vp,large,exclude,∅,0,Set.finite_empty,?_⟩
  intro h B crt _out _late rep
  have big := (separated_values values T ahead).1
  have betaEq : beta X=(n 0:ℚ) := by rw [first]; simp [beta]
  have divide : (κ:ℤ)∣h := by
    have d:=Int.modEq_zero_iff_dvd.mp crt.preparation
    simpa only [ko] using d
  have ah : anchor∣h := (Int.natCast_dvd_natCast.mpr (dvd_mul_right _ _ :
    Nat.factorial 576∣kernelMod r)).trans divide
  constructor
  · intro j t trace p hp
    have all:=selected_trace_orders values unitScale alive vp π o lp lm big exclude (fun d => by
      have := Fact.mk (values.prime _ d.property)
      obtain ⟨z,z2,plus,minus⟩:=CMReduction.exists_oriented_root (oriented.norm d) (oriented.ray16 d) (oriented.ray7 d)
      exact ⟨z,z2,Or.inl ⟨plus,minus⟩⟩) crt rep luc betaEq
    exact (all j p hp).2.1.le
  · apply fixed_depths values alive vp big dv
    intro p fix prime place lie
    rw [betaEq]
    exact integral p prime fix place lie _ _ q h (n 0) n rep ah
  · intro p prime inSet
    have pp : p∈T := by
      rcases inSet with a|b
      · exact Finset.mem_union_left _ a
      · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨prime,b,Int.natAbs_ne_zero.mpr (radicand_nonzero X)⟩)
    have ep := (crt.exact_depth prime (ts.symm ▸ pp)).2
    rw [ao] at ep
    rw [←cast_radicand]
    exact scalar_unit_of_indices (radicand_nonzero X) pp mp rep (by change n 1-1=c; omega) divide dc ep


end
end Sun28.FiniteWitness
#print axioms Sun28.FiniteWitness.selection_of_integral_tests
