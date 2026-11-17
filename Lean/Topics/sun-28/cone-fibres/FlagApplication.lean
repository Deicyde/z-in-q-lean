import ConeFibres

namespace Sun28.ConeFibres
open Finset Sun28.MixedSieve Sun28.QuadricSieve Sun28.SieveTail Sun28.ConeSieve
open Sun28.ContactFactors Sun28.MediumSieve
open scoped Classical
noncomputable section
variable {A : Fin 3 → ℚ} {p : ℕ} [Fact p.Prime]

def actualFlag (p : ℕ) [Fact p.Prime] (i j : ↥(shifts A)) : Finset (Coordinates (ZMod p)) :=
  univ.filter fun x => onCone (gap i j : ZMod p) x ∧ x≠0 ∧
    ∃ k : ↥(shifts A), x.1.1^2+x.1.2^2+(gap k i:ZMod p)*x.2.2^2=0

@[simp] theorem mem_actualFlag {i j : ↥(shifts A)} {x : Coordinates (ZMod p)} :
    x∈actualFlag p i j ↔ onCone (gap i j:ZMod p) x ∧ x≠0 ∧
      ∃ k : ↥(shifts A), x.1.1^2+x.1.2^2+(gap k i:ZMod p)*x.2.2^2=0 := by
  simp [actualFlag]

theorem mem_badFactors_iff (i j : ↥(shifts A)) (P : Finset ℕ) (x : Coordinates ℤ)
    (eq : onCone (gap i j) x) :
    p ∈ badFactors i P x ↔ p∈P ∧ reduction p x∈actualFlag p i j := by
  have castValue (k : ↥(shifts A)) : (p:ℤ)∣value i k x ↔
      (reduction p x).1.1^2+(reduction p x).1.2^2+(gap k i:ZMod p)*(reduction p x).2.2^2=0 := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [value,norm1,reduction,Int.cast_add,Int.cast_pow,Int.cast_mul]
  simp only [badFactors,mem_filter,mem_actualFlag,reduce_cone p eq,true_and,castValue]

def coefficients (p : ℕ) (i : ↥(shifts A)) : Finset (ZMod p) :=
  univ.image fun k : ↥(shifts A) => (gap k i:ZMod p)

private theorem aligned (i j : ↥(shifts A)) :
    actualFlag p i j=flagClasses (gap i j:ZMod p) (coefficients p i) := by
  ext x
  simp only [mem_actualFlag,flagClasses,mem_erase,normWindow,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨eq,nz,k,h⟩
    exact ⟨nz,eq,mem_image.mpr ⟨(gap k i:ZMod p),mem_image.mpr ⟨k,mem_univ _,rfl⟩,
      by dsimp only [norm]; linear_combination -h⟩⟩
  · rintro ⟨nz,eq,h⟩
    obtain ⟨_,hc,h⟩:=mem_image.mp h
    obtain ⟨k,_,rfl⟩:=mem_image.mp hc
    exact ⟨eq,nz,k,by dsimp only [norm] at h; linear_combination -h⟩

theorem actual_flag_card (odd : p≠2) (i j : ↥(shifts A)) (distinct : (gap i j:ZMod p)≠0) :
    ((actualFlag p i j).card:ℤ)=flagPolynomial p (coefficients p i).card := by
  rw [aligned]
  apply flag_classes_card odd distinct
  · exact mem_image.mpr ⟨i,mem_univ _,by simp [gap]⟩
  · exact mem_image.mpr ⟨j,mem_univ _,by simp only [gap,Int.cast_sub]; ring⟩

theorem reduced_gap_ne_zero {d : ℕ} (pos : 0<d) (large : exceptionalBound A d<p)
    {i j : ↥(shifts A)} (diff : i≠j) : (gap i j:ZMod p)≠0 := by
  intro z
  have divides := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp z
  exact (outside_base pos (le_refl _) large i j (gap_ne_zero diff)).2
    (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr divides)

theorem actual_flag_card_above {d : ℕ} (pos : 0<d) (large : exceptionalBound A d<p)
    (odd : p≠2) (i j : ↥(shifts A)) (diff : i≠j) :
    ((actualFlag p i j).card:ℤ)=flagPolynomial p (shifts A).card := by
  rw [actual_flag_card odd i j (reduced_gap_ne_zero pos large diff)]
  have inject : Function.Injective (fun k : ↥(shifts A) => (gap k i:ZMod p)) := by
    intro r s eq
    by_contra h
    apply reduced_gap_ne_zero pos large h
    simp only [gap,Int.cast_sub] at eq ⊢
    linear_combination eq
  simp only [coefficients,card_image_of_injective _ inject,card_univ,Fintype.card_coe]

end
end Sun28.ConeFibres
#print axioms Sun28.ConeFibres.mem_actualFlag
#print axioms Sun28.ConeFibres.mem_badFactors_iff
#print axioms Sun28.ConeFibres.actual_flag_card
#print axioms Sun28.ConeFibres.reduced_gap_ne_zero
#print axioms Sun28.ConeFibres.actual_flag_card_above
