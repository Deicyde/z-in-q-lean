import InverseCutoff
import HybridCount
import LocalProduct
import ElementaryProjection
import SharpMixed
import PrescribedNorm

namespace Sun28.PrimeMass
open Finset Filter Topology Sun28.ContactFactors Sun28.SinglePrime Sun28.ContactSieve
open Sun28.FinitePattern Sun28.PrimeLower Sun28.MediumSieve Sun28.WeightedSelection
open Sun28.Ordinary Sun28.HeightFibres.Sharp Sun28.HeightExtension Sun28.HeightBudget
noncomputable section

def hybridRows (A : Fin 3 → ℚ) (d K L : ℕ) (δ : ℝ) : Prop :=
  ∀ J : ℕ, ∃ j ≥ J, ∃ᶠ t : ℕ in atTop,
    let N := lengthAt t
    let W := rowWidth j N
    δ*((N:ℝ)*W) ≤ hybridMass A d K L N W

/-- The coefficient only has to beat any fixed multiple of the prime tail,
at a sufficiently large cutoff of one's choice. -/
def HybridInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ K ≥ B,
      ∀ (m : ℕ) (D : ℝ), ∃ (L : ℕ) (δ : ℝ), max K m ≤ L ∧ 0 < δ ∧
        D < δ * ((L:ℝ)*Real.log L) ∧ hybridRows (Sun28.RealPoleBounds.fixedScale n) d K L δ

/-- A sufficient estimate with only an inverse first power of the cutoff. -/
def HybridInverseInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ (K : ℕ) (α : ℝ), B ≤ K ∧ 0 < α ∧
      ∀ m : ℕ, ∃ L ≥ max K m,
        hybridRows (Sun28.RealPoleBounds.fixedScale n) d K L (α/(L:ℝ))

theorem hybrid_of_inverse (input : HybridInverseInputs) : HybridInputs := by
  intro X c q n roots d dp B
  obtain ⟨K,α,bk,ap,find⟩ := input X c q n roots d dp B
  exact ⟨K,bk,cofinal_rates ap find⟩

/-- A fixed-base correlation formula would suffice with any positive base
coefficient. Both products and their uniform lower bounds are already formalized. -/
def LocalProductInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ (K : ℕ) (α : ℝ), B ≤ K ∧ 0 < α ∧
      ∀ m : ℕ, ∃ L ≥ max K m,
        let A := Sun28.RealPoleBounds.fixedScale n
        hybridRows A d K L (α *
          ((∏ p ∈ (places K L).attach,
            let _ : Fact p.val.Prime := ⟨(mem_places.mp p.property).2.2⟩
            beta (fun i : ↥(shifts A) => (offset (dilation A) i : ZMod p.val))) *
            ∏ p ∈ places K L,(1-hybridLoss A p)))

theorem hybrid_of_products (input : LocalProductInputs) : HybridInputs := by
  apply hybrid_of_inverse
  intro X c q n roots d dp B
  let A := Sun28.RealPoleBounds.fixedScale n
  obtain ⟨K,α,base,ap,good⟩ := input X c q n roots d dp (max B 2810)
  have big : 2810 ≤ K := (le_max_right _ _).trans base
  refine ⟨K,α/4,(le_max_left _ _).trans base,by positivity,fun m => ?_⟩
  obtain ⟨L,kl,found⟩ := good m
  refine ⟨L,kl,fun J => ?_⟩
  obtain ⟨j,jJ,rows⟩ := found J
  refine ⟨j,jJ,rows.mono (fun t h => ?_)⟩
  have lp : (1:ℝ) ≤ L := by exact_mod_cast (show 1≤L by omega)
  let _ : Nonempty ↥(shifts A) := ⟨⟨_,shift_mem A 0 (a:=0) (by simp [Ordinary.marks])⟩⟩
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have l := mul_le_mul_of_nonneg_left (local_product A K L big) ap.le
  apply le_trans _ l
  calc (α/4)/(L:ℝ) ≤ α/4 := div_le_self (by positivity) lp
       _ = α*(1/4) := by ring

theorem hybrid_surplus (low : HybridInputs) (upper : PrimeUpperInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K₁,C,cn,upp⟩ := upper X c q n roots d κ T dp kp primes two H Y
  let A := Sun28.RealPoleBounds.fixedScale n
  let B := max 2 (max (max (T.sup id) (κ.primeFactors.sup id)) (exceptionalBound A d))
  obtain ⟨K,bk,lower⟩ := low X c q n roots d dp B
  obtain ⟨L,δ,large,δp,margin,counts⟩ := lower K₁ (2*(C*(4*Real.log 4)))
  have kl := (le_max_left K K₁).trans large
  have k2 : 2 ≤ K := (le_max_left _ _).trans bk
  have l2 : 2 ≤ L := k2.trans kl
  have lp : (0:ℝ) < L := by exact_mod_cast (show 0<L by omega)
  have logp := Real.log_pos (show (1:ℝ)<L by exact_mod_cast (show 1<L by omega))
  obtain ⟨J,row⟩ := upp L ((le_max_right _ _).trans large)
  have bound : max (max (T.sup id) (κ.primeFactors.sup id)) (exceptionalBound A d) ≤ K :=
    (le_max_right _ _).trans bk
  have inT (p : ℕ) (hp : p ∈ T) : p ≤ K :=
    (Finset.le_sup (f:=id) hp).trans ((le_max_left _ _).trans ((le_max_left _ _).trans bound))
  have inAux (p : ℕ) (hp : p ∈ κ.primeFactors) : p ≤ K :=
    (Finset.le_sup (f:=id) hp).trans ((le_max_right _ _).trans ((le_max_left _ _).trans bound))
  have ex : exceptionalBound A d ≤ K := (le_max_right _ _).trans bound
  obtain ⟨I,fit⟩ := fixed_rows (P:=fun N W => hybridMass A d K L N W ≤
    mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W)) (fun w short =>
      eventually_hybrid_le_main dp k2 ex inT inAux w short)
  refine ⟨L,surplus_of_mass (hybridMass A d K L) counts
    ⟨I,fun j hj => length_grows.eventually (fit j hj)⟩ (sharp_transfer l2 cn row) k2 kl inT inAux δp ?_⟩
  rw [div_div,div_lt_iff₀ (mul_pos logp lp)]
  linarith [show δ*((L:ℝ)*Real.log L) = 2*(δ/2*(Real.log L*L)) by ring]

/-- The three remaining arithmetic assertions are explicit parameters of the fixed polynomial. -/
theorem integer_projection (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (characters : QuadraticCharacterDiscriminants)
    (quadric : ConeCount.PublishedQuadricCount) (height : HeightRefinement.Sharp.Residual)
    (lower : HybridInputs) (points : PointDescent.NormResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) := by
  have h := (HeightRefinement.Sharp.original_iff_sharp units pell classes characters).mpr height
  have mass := hybrid_surplus lower (ConeSieve.row_of_congruences (ConeCount.upper_sieve quadric))
  exact TwistExtension.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp h) mass
    (PrescribedPoints.core_iff_residual.mp (PointDescent.core_of_norm_residual points)) x

end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.hybrid_of_inverse
#print axioms Sun28.PrimeMass.hybrid_of_products
#print axioms Sun28.PrimeMass.hybrid_surplus
#print axioms Sun28.PrimeMass.integer_projection
