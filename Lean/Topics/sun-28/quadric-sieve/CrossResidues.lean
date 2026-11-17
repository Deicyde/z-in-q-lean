import QuadricRecords

namespace Sun28.QuadricSieve
open Finset Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.NormSieve
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

def crossSet (p : ℕ) [Fact p.Prime] (κ : ZMod p) : Finset (Coordinates (ZMod p)) :=
  univ.filter fun x => onCone κ x ∧ (x.1.1+1)^2+x.1.2^2=0 ∧ (x.2.1.1-1)^2+x.2.1.2^2=0

/-- On fixing w and the first norm t, there are at most two points of the
plus fibre over t and at most two of the minus fibre over t-κ w². -/
theorem cross_card_le {p : ℕ} [Fact p.Prime] (odd : p≠2) (κ : ZMod p) :
    (crossSet p κ).card ≤ 4*p^2 := by
  let I : Finset (ZMod p × ZMod p) := univ
  let choices (u : ZMod p × ZMod p) :=
    badFibre p u.1 true ×ˢ badFibre p (u.1-κ*u.2^2) false
  let assemble (u : ZMod p × ZMod p) (z : (ZMod p × ZMod p) × (ZMod p × ZMod p)) :
    Coordinates (ZMod p) := (z.1,z.2,u.2)
  have incl : crossSet p κ ⊆ I.biUnion (fun u => (choices u).image (assemble u)) := by
    rintro ⟨⟨a,b⟩,⟨c,e⟩,w⟩ h
    obtain ⟨q,hp,hm⟩ := (mem_filter.mp h).2
    change a^2+b^2-c^2-e^2=κ*w^2 at q
    apply mem_biUnion.mpr
    refine ⟨(a^2+b^2,w),mem_univ _,mem_image.mpr ⟨((a,b),(c,e)),?_,rfl⟩⟩
    apply mem_product.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,rfl,hp⟩,mem_filter.mpr ⟨mem_univ _,?_,?_⟩⟩
    · change c^2+e^2=a^2+b^2-κ*w^2
      linear_combination -q
    · simpa only [Bool.false_eq_true,ite_false,sub_eq_add_neg] using hm
  have bound (u) : ((choices u).image (assemble u)).card ≤ 4 := by
    apply card_image_le.trans
    dsimp only [choices]
    rw [card_product]
    exact Nat.mul_le_mul (two_residues odd _ true) (two_residues odd _ false)
  calc
    _ ≤ _ := card_le_card incl
    _ ≤ ∑ u∈I,((choices u).image (assemble u)).card := card_biUnion_le
    _ ≤ ∑ _∈I,4 := sum_le_sum (fun u _=>bound u)
    _ = _ := by simp [I,pow_two];ring

theorem cross_nonzero {p : ℕ} [Fact p.Prime] {κ : ZMod p} {x} (h : x∈crossSet p κ) : x≠0 := by
  intro e
  have hp := (mem_filter.mp h).2.2.1
  subst x
  change ((0:ZMod p)+1)^2+0^2=0 at hp
  simp at hp

private theorem adjacent_residue {p : ℕ} [Fact p.Prime] (z : Gaussian) (s : Bool)
    (h : p∣adjacentNorm z s) :
    ((z.1:ZMod p)+(if s then 1 else -1))^2+(z.2:ZMod p)^2=0 := by
  have e := (ZMod.natCast_eq_zero_iff _ _).mpr h
  cases s <;> simpa [adjacentNorm,gaussian_residue,realResidue,imagResidue,sub_eq_add_neg] using e

theorem cross_record {A : Fin 3→ℚ} {d p : ℕ} {H Y : ℝ} [Fact p.Prime]
    (a : Candidate A d H Y) (i j : ↥(shifts A)) (ij : i≠j)
    (plus : p∣adjacentNorm (a.gaussian i) true) (minus : p∣adjacentNorm (a.gaussian j) false) :
    gap i j≠0 ∧ onCone (gap i j) (integerPoint a i j) ∧
      reduction p (integerPoint a i j)∈crossSet p (gap i j) := by
  have q:=integer_cone a i j
  refine ⟨gap_ne_zero ij,q,mem_filter.mpr ⟨mem_univ _,reduce_cone p q,?_,?_⟩⟩
  · exact adjacent_residue (a.gaussian i) true plus
  · simpa [reduction,integerPoint,sub_eq_add_neg] using adjacent_residue (a.gaussian j) false minus

end
end Sun28.QuadricSieve
#print axioms Sun28.QuadricSieve.cross_card_le
#print axioms Sun28.QuadricSieve.cross_nonzero
#print axioms Sun28.QuadricSieve.cross_record
