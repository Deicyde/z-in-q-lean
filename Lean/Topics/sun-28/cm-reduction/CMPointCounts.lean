import OddGaussianCoordinate
import ModelTransport

namespace Sun28.CMReduction
open ZInQ ZInQ.Density ManuscriptV15.Arithmetic

theorem selected_class {p : ℕ} {z : Gaussian} (norm : gaussianNorm z=p)
    (r16 : gaussianCongruent 16 z (9,0)) (r7 : gaussianCongruent 7 z (1,3)) :
    InClass p := by
  have pn : (p:ℤ)=z.1^2+z.2^2 := (congrArg (fun n : ℕ=>(n:ℤ)) norm).symm.trans (archive_norm z)
  obtain ⟨a,b⟩:=r16
  obtain ⟨c,d⟩:=r7
  have e8 : (p:ℤ) ≡ 1 [ZMOD 8] := by
    rw [pn]
    exact ((((a.pow 2).add (b.pow 2)).of_dvd (by decide : (8:ℤ)∣16))).trans (by decide)
  have e7 : (p:ℤ) ≡ 3 [ZMOD 7] := by
    rw [pn]
    exact ((c.pow 2).add (d.pow 2)).trans (by decide)
  exact ⟨Int.natCast_modEq_iff.mp e8,Or.inl (Int.natCast_modEq_iff.mp e7)⟩

private theorem adj_norms (z : Gaussian) (p : ℕ) (norm : gaussianNorm z=p) :
    (adjacentNorm z true:ℤ)=p+1+2*z.1 ∧ (adjacentNorm z false:ℤ)=p+1-2*z.1 := by
  have n:=archive_norm z
  rw [norm] at n
  constructor
  · unfold adjacentNorm
    rw [archive_norm,n]
    simp
    ring
  · unfold adjacentNorm
    rw [archive_norm,n]
    simp
    ring

/-- At a given square root, the point counts give the two Gaussian norms in some order. -/
theorem unordered_counts {p : ℕ} [pp : Fact p.Prime] {z : Gaussian}
    (norm : gaussianNorm z=p) (r16 : gaussianCongruent 16 z (9,0)) (r7 : gaussianCongruent 7 z (1,3))
    {r : ZMod p} (hr : r^2=2) :
    (pointCount p (-(3-r)^2)=adjacentNorm z true ∧ pointCount p (-(3+r)^2)=adjacentNorm z false) ∨
    (pointCount p (-(3-r)^2)=adjacentNorm z false ∧ pointCount p (-(3+r)^2)=adjacentNorm z true) := by
  have cls:=selected_class norm r16 r7
  have n:=archive_norm z
  rw [norm] at n
  obtain ⟨e,hce⟩:=exists_sq_add_sq cls
  have b : z.2%2=0 := r16.2.of_dvd (by decide : (2:ℤ)∣16)
  have sign := odd_coordinate_unique pp.out n.symm hce.symm b (cp_odd cls)
  obtain ⟨plus,minus⟩:=adj_norms z p norm
  obtain ⟨a,b⟩:=pointCount_transport cls.ne_two hr
  have pair:=pointCount_pair cls hr
  rw [a,b] at pair
  rcases sign with sign|sign <;> rcases pair with left|right
  · right; constructor <;> apply (Nat.cast_inj (R:=ℤ)).mp <;> linarith [left.1,left.2]
  · left; constructor <;> apply (Nat.cast_inj (R:=ℤ)).mp <;> linarith [right.1,right.2]
  · left; constructor <;> apply (Nat.cast_inj (R:=ℤ)).mp <;> linarith [left.1,left.2]
  · right; constructor <;> apply (Nat.cast_inj (R:=ℤ)).mp <;> linarith [right.1,right.2]

/-- Choose the square root whose reduction has the plus cardinality. The other is its conjugate. -/
theorem exists_oriented_root {p : ℕ} [Fact p.Prime] {z : Gaussian} (norm : gaussianNorm z=p)
    (r16 : gaussianCongruent 16 z (9,0)) (r7 : gaussianCongruent 7 z (1,3)) :
    ∃ r : ZMod p, r^2=2 ∧ pointCount p (-(3-r)^2)=adjacentNorm z true ∧
      pointCount p (-(3+r)^2)=adjacentNorm z false := by
  have cls:=selected_class norm r16 r7
  obtain ⟨r,sqroot⟩:=(ZMod.exists_sq_eq_two_iff (p:=p) cls.ne_two).mpr (Or.inl cls.1)
  have hr : r^2=2 := by rw [sq]; exact sqroot.symm
  rcases unordered_counts norm r16 r7 hr with h|h
  · exact ⟨r,hr,h⟩
  · refine ⟨-r,by simpa using hr,?_,?_⟩
    · simpa only [sub_neg_eq_add] using h.2
    · simpa only [sub_eq_add_neg] using h.1

end Sun28.CMReduction
#print axioms Sun28.CMReduction.selected_class
#print axioms Sun28.CMReduction.unordered_counts
#print axioms Sun28.CMReduction.exists_oriented_root
