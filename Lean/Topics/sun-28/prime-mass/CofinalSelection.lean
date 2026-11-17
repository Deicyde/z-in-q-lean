import FixedRows
import SharpTransfer

namespace Sun28.PrimeMass
open Finset Filter Topology Sun28.SinglePrime Sun28.ContactFactors Sun28.ContactSieve
open Sun28.WeightedSelection Sun28.MediumSieve Sun28.FinitePattern
noncomputable section

/-- For arbitrarily narrow fixed rows there are arbitrarily late successful scales. -/
def frequentRows (A : Fin 3 → ℚ) (d K L : ℕ) (δ : ℝ) : Prop :=
  ∀ J : ℕ, ∃ j ≥ J, ∃ᶠ t : ℕ in atTop,
    let N := lengthAt t
    let W := rowWidth j N
    δ*((N:ℝ)*W) ≤ patternMass A d K L N W

/-- The coefficient only has to beat any fixed multiple of the prime tail,
at a sufficiently large cutoff of one's choice. -/
def CofinalInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ K ≥ B,
      ∀ (m : ℕ) (D : ℝ), ∃ (L : ℕ) (δ : ℝ), max K m ≤ L ∧ 0 < δ ∧
        D < δ * ((L:ℝ)*Real.log L) ∧ frequentRows (Sun28.RealPoleBounds.fixedScale n) d K L δ

theorem surplus_of_mass {A : Fin 3 → ℚ} {K L d κ J : ℕ} {T : Finset ℕ} {H Y C δ : ℝ}
    (mass : ℕ → ℕ → ℝ)
    (success : ∀ J : ℕ, ∃ j ≥ J, ∃ᶠ t : ℕ in atTop,
      δ*((lengthAt t:ℝ)*rowWidth j (lengthAt t)) ≤ mass (lengthAt t) (rowWidth j (lengthAt t)))
    (fits : ∃ I : ℕ, ∀ j ≥ I, ∀ᶠ t : ℕ in atTop,
      mass (lengthAt t) (rowWidth j (lengthAt t)) ≤
        mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) (lengthAt t) (rowWidth j (lengthAt t)))) (middle : LogRow A d H Y T κ L J C)
    (big : 2 ≤ K) (kl : K ≤ L) (tin : ∀ p ∈ T,p ≤ K) (ain : ∀ p ∈ κ.primeFactors,p ≤ K)
    (dp : 0 < δ) (gap : C/(L:ℝ) < δ/2) :
    ∃ S : Finset (Record A d H Y), surplus T κ L S := by
  obtain ⟨I,record⟩ := fits
  obtain ⟨r,hr⟩ := exists_nat_gt (4/δ)
  obtain ⟨j,large,often⟩ := success (max J (max I r))
  have m := middle j ((le_max_left _ _).trans large)
  have g := record j ((le_max_left _ _).trans ((le_max_right _ _).trans large))
  have rj : (r:ℝ) ≤ j := by exact_mod_cast (le_max_right I r).trans ((le_max_right _ _).trans large)
  have err : 1/((j:ℝ)+1) < δ/4 := by
    apply (div_lt_iff₀ (by positivity : 0<(j:ℝ)+1)).mpr
    nlinarith only [(div_lt_iff₀ dp).mp hr,mul_le_mul_of_nonneg_left rj dp.le,dp]
  have near := (relative_error A).eventually_lt_const (by linarith : 0 < δ/4)
  have wide := length_grows.eventually (row_grows j 1)
  have cut := tendsto_atTop.mp (cutoff_grows A) L
  obtain ⟨t,lower,mid,main,small,width,lr,within⟩ :=
    (often.and_eventually (m.and (g.and (near.and (wide.and (cut.and (cutoff_within A))))))).exists
  let N := lengthAt t
  let W := rowWidth j N
  let S := box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let Z : ℝ := (N:ℝ)*W
  have posN : 0 < N := by dsimp [N,lengthAt]; exact pow_pos (side_pos t) 2
  have posW : 0 < W := width
  have zp : 0 < Z := by dsimp [Z]; positivity
  have hi := log_tail (A:=A) (d:=d) (H:=H) (Y:=Y) T κ t W
    ((Nat.div_le_self _ _).trans_eq (Nat.sqrt_eq' _)) (by omega) within
    (fun p h => (tin p h).trans (kl.trans lr)) (fun p h => (ain p h).trans (kl.trans lr))
  have md : middleMass T κ L (logCutoff A t) S ≤ (C/(L:ℝ)+1/((j:ℝ)+1))*Z := mid
  have lo : δ*Z ≤ mainMass T κ L S := lower.trans main
  refine ⟨S,?_⟩
  change removedMass T κ L S < mainMass T κ L S
  rw [split_removed _ _ _ _ lr _]
  apply (add_le_add md hi).trans_lt
  apply lt_of_lt_of_le _ lo
  rw [←add_mul]
  exact mul_lt_mul_of_pos_right (by linarith) zp

theorem surplus_of_row {A : Fin 3 → ℚ} {K L d κ J : ℕ} {T : Finset ℕ} {H Y C δ : ℝ}
    (counts : frequentRows A d K L δ) (middle : LogRow A d H Y T κ L J C)
    (big : 2 ≤ K) (kl : K ≤ L) (tin : ∀ p ∈ T,p ≤ K) (ain : ∀ p ∈ κ.primeFactors,p ≤ K)
    (dp : 0 < δ) (gap : C/(L:ℝ) < δ/2) :
    ∃ S : Finset (Record A d H Y), surplus T κ L S :=
  surplus_of_mass (patternMass A d K L) counts (fixed_pattern tin ain) middle big kl tin ain dp gap

theorem positive_surplus (low : CofinalInputs) (upper : PrimeUpperInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K₁,C,cn,upp⟩ := upper X c q n roots d κ T dp kp primes two H Y
  let B := max 2 (max (T.sup id) (κ.primeFactors.sup id))
  obtain ⟨K,bk,lower⟩ := low X c q n roots d dp B
  obtain ⟨L,δ,large,δp,margin,counts⟩ := lower K₁ (2*(C*(4*Real.log 4)))
  have kl := (le_max_left K K₁).trans large
  have k2 : 2 ≤ K := (le_max_left _ _).trans bk
  have l2 : 2 ≤ L := k2.trans kl
  have lp : (0:ℝ) < L := by exact_mod_cast (show 0<L by omega)
  have logp := Real.log_pos (show (1:ℝ)<L by exact_mod_cast (show 1<L by omega))
  obtain ⟨J,row⟩ := upp L ((le_max_right _ _).trans large)
  refine ⟨L,surplus_of_row counts (sharp_transfer l2 cn row) k2 kl ?_ ?_ δp ?_⟩
  · intro p hp; exact (Finset.le_sup (f:=id) hp).trans ((le_max_left _ _).trans ((le_max_right _ _).trans bk))
  · intro p hp; exact (Finset.le_sup (f:=id) hp).trans ((le_max_right _ _).trans ((le_max_right _ _).trans bk))
  · rw [div_div,div_lt_iff₀ (mul_pos logp lp)]
    linarith [show δ*((L:ℝ)*Real.log L) = 2*(δ/2*(Real.log L*L)) by ring]
end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.surplus_of_mass
#print axioms Sun28.PrimeMass.surplus_of_row
#print axioms Sun28.PrimeMass.positive_surplus
