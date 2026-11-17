import FixedRayPrimes
import OrdinaryTransfer

namespace Sun28.PrimeModel
open Finset Filter Sun28.PrimeValues Sun28.PrimeTransfer
open scoped Classical
noncomputable section

private def normEmbedding (K : ℕ) : FixedIdeal K ↪ ℕ :=
  (fixed_prime_equiv K).toEmbedding.trans (Function.Embedding.subtype _)

/-- Every fixed-ray prime ideal whose absolute norm lies in the specified finite set. -/
def idealsIn (K : ℕ) (s : Finset ℕ) : Finset (FixedIdeal K) :=
  s.preimage (normEmbedding K) (normEmbedding K).injective.injOn

@[simp] theorem mem_idealsIn {K : ℕ} {s : Finset ℕ} (J : FixedIdeal K) :
    J∈idealsIn K s ↔ norm J.val∈s := by
  exact mem_preimage

/-- Exact equality, including the ramified prime and every degree-two candidate. -/
theorem ray_log_sum (K : ℕ) (s : Finset ℕ) :
    (∑ J ∈ idealsIn K s, Real.log (norm J.val:ℕ)) = ∑ p ∈ s, classWeight K p := by
  have inRange (p : ℕ) : p∈Set.range (normEmbedding K) ↔ oneClass K p := by
    constructor
    · rintro ⟨J,rfl⟩
      exact (fixed_prime_equiv K J).2
    · intro h
      obtain ⟨J,eq⟩ := (fixed_prime_equiv K).surjective ⟨p,h⟩
      exact ⟨J,congrArg Subtype.val eq⟩
  change (∑ J ∈ s.preimage _ _, Real.log ((normEmbedding K J:ℕ):ℝ)) = _
  rw [←sum_image (f:=fun p:ℕ => Real.log (p:ℝ)) (normEmbedding K).injective.injOn, image_preimage, sum_filter]
  apply sum_congr rfl
  intro p _
  rw [classWeight, inRange]

/-- A prefix sum over the actual prime ideals in this ray. -/
def idealTheta (K X : ℕ) : ℝ := ∑ J∈idealsIn K (range (X+1)), Real.log (norm J.val:ℕ)

/-- The logarithmically weighted consequence of Landau's fixed-modulus ray-class theorem.
The strict ray class number of Q(i) is the order of the fixed finite coordinate group. -/
def RayPrimeIdealTheorem : Prop :=
  ∀ K : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
    |idealTheta K X - (X:ℝ)/Nat.card (Sun28.Reciprocity.idealRay (Sun28.Reciprocity.moduli K))| ≤ ε*X

private theorem interval_le_band (K N V : ℕ) (vp : 0 < V) (room : 2*V ≤ N) :
    idealTheta K (2*N/3)-idealTheta K (5*N/8) ≤ ∑ p∈band N V, classWeight K p := by
  let A:=range (5*N/8+1)
  let B:=range (2*N/3+1)
  have sub : A⊆B := by apply range_mono; omega
  have eqA := ray_log_sum K A
  have eqB := ray_log_sum K B
  change (∑ J∈idealsIn K B, _) - (∑ J∈idealsIn K A, _) ≤ _
  rw [eqA,eqB,←sum_sdiff_eq_sub sub]
  let C:=(B \ A).filter (oneClass K)
  have filt : ∑ p∈B \ A, classWeight K p = ∑ p∈C, classWeight K p := by
    symm
    exact sum_subset (filter_subset ..) (fun p hp out => by
      have no : ¬oneClass K p := fun yes => out (mem_filter.mpr ⟨hp,yes⟩)
      simp [classWeight,no])
  rw [filt]
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => (class_weight_le K p).1)
  intro p hp
  obtain ⟨ins,qualified⟩ := mem_filter.mp hp
  obtain ⟨hi,lo⟩ := mem_sdiff.mp ins
  have high := mem_range.mp hi
  have low : ¬p < 5*N/8+1 := fun a=>lo (mem_range.mpr a)
  change p < 2*N/3+1 at high
  have pv : V < p := by omega
  have cop : V.Coprime p := (qualified.1.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt vp pv)).symm
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,by omega,by omega,cop⟩

/-- On [5N/8,2N/3] the main term is N/(24h). A common 1/(100h) works for
every fixed V as soon as the two endpoints exceed Landau's threshold and V. -/
theorem one_prime_of_landau (landau : RayPrimeIdealTheorem) : OnePrimeDensity := by
  intro K
  let h := Nat.card (Sun28.Reciprocity.idealRay (Sun28.Reciprocity.moduli K))
  have hp : 0 < h := by
    have e:= Sun28.Reciprocity.idealCoordinates (Sun28.Reciprocity.moduli K)
      (Sun28.Reciprocity.level_coprime K)
    change 0 < Nat.card (Sun28.Reciprocity.idealRay (Sun28.Reciprocity.moduli K))
    rw [Nat.card_congr e.toEquiv]
    let (i : Sun28.Reciprocity.Slot K) : NeZero (Sun28.Reciprocity.moduli K i) := ⟨i.2.1.ne_zero⟩
    let (i : Sun28.Reciprocity.Slot K) : Finite (Sun28.RayDensity.GR (Sun28.Reciprocity.moduli K i)) :=
      Finite.of_injective (fun z => (z.re,z.im)) (fun _ _ h => QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    exact Nat.card_pos
  have hr : (0:ℝ) < h := by exact_mod_cast hp
  let ε : ℝ := 1/(100*h)
  have ep : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,ep,?_⟩
  intro V vp
  obtain ⟨L,large⟩ := eventually_atTop.mp (landau K ε ep)
  filter_upwards [eventually_ge_atTop (2*V+24*L+192)] with N hn
  have lo := abs_le.mp (large (5*N/8) (by omega))
  have hi := abs_le.mp (large (2*N/3) (by omega))
  have bounds := interval_le_band K N V vp (by omega)
  have lowN : ((5*N/8:ℕ):ℝ)*8 ≤ 5*(N:ℝ) := by exact_mod_cast Nat.div_mul_le_self (5*N) 8
  have highN : 2*(N:ℝ) ≤ ((2*N/3:ℕ):ℝ)*3+2 := by exact_mod_cast (show 2*N≤2*N/3*3+2 by omega)
  have eachA : ((5*N/8:ℕ):ℝ) ≤ N := by exact_mod_cast (show 5*N/8≤N by omega)
  have eachB : ((2*N/3:ℕ):ℝ) ≤ N := by exact_mod_cast (show 2*N/3≤N by omega)
  have big : (192:ℝ) ≤ N := by exact_mod_cast (show 192≤N by omega)
  have estA := lo.2
  have estB := hi.1
  change idealTheta K _ - _/(h:ℝ) ≤ (1/(100*h))*_ at estA
  change -((1/(100*(h:ℝ)))*_) ≤ idealTheta K _ - _/(h:ℝ) at estB
  dsimp only [ε]
  apply (le_trans _ bounds)
  field_simp [hr.ne', hr] at estA estB ⊢
  nlinarith only [estA,estB,lowN,highN,eachA,eachB,big]

/-- In the lower-count application the only ray-specific one-variable input is now
the classical prime ideal theorem for one fixed ideal class at a time. -/
theorem hybrid_of_landau (grid : PublishedRecurrence) (landau : RayPrimeIdealTheorem)
    (model : OrdinaryModelInputs) (upper : RelativeUpperInputs) :
    Sun28.PrimeMass.HybridInputs :=
  hybrid_of_ordinary grid (one_prime_of_landau landau) model upper

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.mem_idealsIn
#print axioms Sun28.PrimeModel.ray_log_sum
#print axioms Sun28.PrimeModel.one_prime_of_landau
#print axioms Sun28.PrimeModel.hybrid_of_landau
