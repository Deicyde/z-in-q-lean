import ConeRecords
import ConeDenominator

namespace Sun28.ConeSieve
open Finset Sun28.QuadricSieve Sun28.SinglePrime Sun28.MediumSieve Sun28.ContactFactors
open Sun28.WeightedSelection Sun28.SieveTail Sun28.MixedSieve
open scoped Classical
noncomputable section

def residues (p : ℕ) [Fact p.Prime] (κ : ℤ) :=
  diagonalSet p (κ:ZMod p) ∪ crossSet p (κ:ZMod p)

theorem residues_card (p : ℕ) [Fact p.Prime] (odd : p≠2) (κ : ℤ) :
    (residues p κ).card≤8*p^2 :=
  (card_union_le ..).trans (by linarith only [diagonal_card_le p (κ:ZMod p),cross_card_le odd (κ:ZMod p)])

def lattice {A : Fin 3→ℚ} (p : ℕ) [Fact p.Prime] (i j : ↥(shifts A)) (N W : ℕ) :=
  (region i j N W).filter fun x=>gap i j≠0 ∧ reduction p x∈residues p (gap i j)

theorem record_cover {A : Fin 3→ℚ} (one : A 0=1) {d N W p κ : ℕ} {H Y : ℝ} [Fact p.Prime]
    (odd : p≠2) (T : Finset ℕ) (out : p∉T) (aux : p∉κ.primeFactors)
    {a : Candidate A d H Y} (ha : a∈box N W) (bad : ¬atPrime a.gaussian T κ p) :
    ∃ i j : ↥(shifts A), integerPoint a i j ∈ lattice p i j N W := by
  have h:=atPrime_iff_fibre a T κ p odd out aux
  obtain ⟨i,j,plus,minus⟩:=(fibre_obstructed_iff a p).mp
    (Classical.not_not.mp (fun good=>bad (h.mpr good)))
  by_cases eq : i=j
  · subst j
    obtain ⟨j,ij⟩:=auxiliary_shift one i
    obtain ⟨gap',_,coll⟩:=diagonal_record odd a i j ij plus minus
    exact ⟨i,j,mem_filter.mpr ⟨record_region ha i j,gap',mem_union_left _ coll⟩⟩
  · obtain ⟨gap',_,coll⟩:=cross_record a i j eq plus minus
    exact ⟨i,j,mem_filter.mpr ⟨record_region ha i j,gap',mem_union_right _ coll⟩⟩

/-- Domination by any finitely supported nonnegative upper weight on the cone.
The point of allowing an arbitrary support is to use smooth majorants of a sharp box. -/
structure Majorant {A : Fin 3→ℚ} (p : ℕ) [Fact p.Prime] (i j : ↥(shifts A)) (N W : ℕ) where
  support : Finset (Coordinates ℤ)
  weight : Coordinates ℤ → ℝ
  nonneg : ∀ x∈support,0≤weight x
  contains : lattice p i j N W ⊆ support
  majorizes : ∀ x∈lattice p i j N W,1≤weight x

theorem one_count_le {A : Fin 3→ℚ} (one : A 0=1) {d N W p κ : ℕ} {H Y : ℝ} [Fact p.Prime]
    (odd : p≠2) (T : Finset ℕ) (out : p∉T) (aux : p∉κ.primeFactors)
    (P : ↥(shifts A) → ↥(shifts A) → Finset ℕ)
    (pr : ∀ i j q, q∈P i j → q.Prime)
    (large : ∀ a∈box (A:=A) (d:=d) (H:=H) (Y:=Y) N W, ∀ i j q, q∈P i j → ∀ k : ↥(shifts A),q<a.values.value k.val)
    (F : ∀ i j : ↥(shifts A), Majorant p i j N W) :
    (oneCount T κ p (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W):ℝ) ≤
    ∑ i,∑ j,mass (F i j).support (F i j).weight (badFactors i (P i j)) (fun U=>indicator (U=∅)) := by
  classical
  let B:=box (A:=A) (d:=d) (H:=H) (Y:=Y) N W
  let lost:=B.filter fun a=>¬atPrime a.gaussian T κ p
  let hits:=fun (k:↥(shifts A)×↥(shifts A))=>B.filter fun a=>integerPoint a k.1 k.2∈lattice p k.1 k.2 N W
  have cover : lost⊆univ.biUnion hits := by
    intro a ha;obtain ⟨hb,bad⟩:=mem_filter.mp ha
    obtain ⟨i,j,h⟩:=record_cover one odd T out aux hb bad
    exact mem_biUnion.mpr ⟨(i,j),mem_univ _,mem_filter.mpr ⟨hb,h⟩⟩
  have count:= (card_le_card cover).trans card_biUnion_le
  have hit (k : ↥(shifts A)×↥(shifts A)) :
      ((hits k).card:ℝ) ≤ mass (F k.1 k.2).support (F k.1 k.2).weight
        (badFactors k.1 (P k.1 k.2)) (fun U=>indicator (U=∅)) := by
    let S:=hits k
    let f:=fun a : Candidate A d H Y=>integerPoint a k.1 k.2
    let I:=S.image f
    let M:=F k.1 k.2
    let obs:=badFactors k.1 (P k.1 k.2)
    have inject : Set.InjOn f (↑S) := (box_injective N W k.1 k.2).mono (by intro _ h;exact (mem_filter.mp h).1)
    have fromI (x : Coordinates ℤ) (hx : x∈I) : x∈lattice p k.1 k.2 N W ∧ obs x=∅ := by
      obtain ⟨a,ha,rfl⟩:=mem_image.mp hx
      obtain ⟨hb,coll⟩:=mem_filter.mp ha
      exact ⟨coll,prime_survives a k.1 k.2 _ (pr k.1 k.2) (fun q h r=>large a hb _ _ q h r)⟩
    calc _ = ∑ _∈I,(1:ℝ) := by simp [I,card_image_of_injOn inject,S]
         _ ≤ ∑ x∈I,M.weight x*indicator (obs x=∅) := by
            apply sum_le_sum;intro x hx; obtain ⟨h,e⟩:=fromI x hx
            simpa [indicator,e] using M.majorizes x h
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg
           (fun x hx=>M.contains (fromI x hx).1) (fun x hx _=>mul_nonneg (M.nonneg x hx) (by unfold indicator;split <;> norm_num))
  calc _ ≤ ∑ k : ↥(shifts A)×↥(shifts A),((hits k).card:ℝ) := by exact_mod_cast count
       _ ≤ ∑ k : ↥(shifts A)×↥(shifts A),mass (F k.1 k.2).support (F k.1 k.2).weight (badFactors k.1 (P k.1 k.2)) (fun U=>indicator (U=∅)) := sum_le_sum fun k _=>hit k
       _ = _ := Fintype.sum_prod_type _

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.residues_card
#print axioms Sun28.ConeSieve.record_cover
#print axioms Sun28.ConeSieve.one_count_le
