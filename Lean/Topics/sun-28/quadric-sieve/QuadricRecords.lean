import QuadricResidues
import MixedChart
import BoxRecords

namespace Sun28.QuadricSieve
open Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.NormSieve Sun28.SinglePrime
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

def integerPoint (a : Candidate A d H Y) (i j : ↥(shifts A)) : Coordinates ℤ :=
  (a.gaussian i,a.gaussian j,a.v)

def reduction (p : ℕ) (x : Coordinates ℤ) : Coordinates (ZMod p) :=
  ((x.1.1,x.1.2),(x.2.1.1,x.2.1.2),x.2.2)

theorem integer_cone (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    onCone (gap i j) (integerPoint a i j) := by
  have hn (b : Gaussian) : (gaussianNorm b:ℤ)=b.1^2+b.2^2 := Int.natAbs_of_nonneg (by positivity)
  have e:=norm_gap a i j
  rw [hn,hn] at e
  change (a.gaussian i).1^2+(a.gaussian i).2^2-(a.gaussian j).1^2-(a.gaussian j).2^2=gap i j*(a.v:ℤ)^2
  linear_combination e

/-- A literal integral point determines the original numerical pair and hence its unique box record. -/
theorem box_injective (N W : ℕ) (i j : ↥(shifts A)) :
    Set.InjOn (fun a : Candidate A d H Y=>integerPoint a i j) (↑(box (A:=A) (d:=d) (H:=H) (Y:=Y) N W) : Set (Candidate A d H Y)) := by
  intro a ha b hb eq
  have v' := congrArg (fun x : Coordinates ℤ=>x.2.2) eq
  have v : a.v=b.v := by exact_mod_cast (show (a.v:ℤ)=(b.v:ℤ) from v')
  have g := congrArg (fun x : Coordinates ℤ=>gaussianNorm x.1) eq
  change gaussianNorm (a.gaussian i)=gaussianNorm (b.gaussian i) at g
  rw [a.rays.norm i,b.rays.norm i] at g
  have gu := congrArg (fun z : ℕ=>(z:ℤ)) g
  rw [a.values.equation i.val i.property,b.values.equation i.val i.property,v] at gu
  exact box_unique ha hb (by omega) v

theorem reduce_cone {κ : ℤ} {x : Coordinates ℤ} (p : ℕ) (h : onCone κ x) :
    onCone (κ:ZMod p) (reduction p x) := by
  change x.1.1^2+x.1.2^2-x.2.1.1^2-x.2.1.2^2=κ*x.2.2^2 at h
  simpa only [onCone,reduction,Int.cast_mul,Int.cast_add,Int.cast_sub,Int.cast_pow] using
    congrArg (fun z : ℤ=>(z:ZMod p)) h

theorem diagonal_record {p : ℕ} [Fact p.Prime] (odd : p≠2) (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (ij : i≠j)
    (plus : p∣adjacentNorm (a.gaussian i) true) (minus : p∣adjacentNorm (a.gaussian i) false) :
    gap i j≠0 ∧ onCone (gap i j) (integerPoint a i j) ∧
      reduction p (integerPoint a i j)∈diagonalSet p (gap i j) := by
  have h:=integer_cone a i j
  have coord:=(diagonal_iff odd (a.gaussian i)).mp ⟨plus,minus⟩
  exact ⟨gap_ne_zero ij,h,Finset.mem_filter.mpr ⟨Finset.mem_univ _,reduce_cone p h,coord⟩⟩

theorem auxiliary_shift (one : A 0=1) (i : ↥(shifts A)) : ∃ j : ↥(shifts A), i≠j := by
  by_contra! hall
  have size : (shifts A).card≤1 := Finset.card_le_one.mpr (fun a ha b hb => by
    have e := (hall ⟨a,ha⟩).symm.trans (hall ⟨b,hb⟩)
    exact congrArg Subtype.val e)
  have enough:=enough_shifts A one
  omega

theorem literal_diagonal {p : ℕ} [Fact p.Prime] (odd : p≠2) (n : Fin 4→ℤ)
    (a : Candidate (Sun28.RealPoleBounds.fixedScale n) d H Y)
    (i : ↥(shifts (Sun28.RealPoleBounds.fixedScale n)))
    (plus : p∣adjacentNorm (a.gaussian i) true) (minus : p∣adjacentNorm (a.gaussian i) false) :
    ∃ j, gap i j≠0 ∧ onCone (gap i j) (integerPoint a i j) ∧
      reduction p (integerPoint a i j)∈diagonalSet p (gap i j) :=
  (auxiliary_shift (by simp [Sun28.RealPoleBounds.fixedScale,Sun28.Ordinary.scaleRoot]) i).elim
    (fun j h=>⟨j,diagonal_record odd a i j h plus minus⟩)

end
end Sun28.QuadricSieve
#print axioms Sun28.QuadricSieve.integer_cone
#print axioms Sun28.QuadricSieve.box_injective
#print axioms Sun28.QuadricSieve.reduce_cone
#print axioms Sun28.QuadricSieve.diagonal_record
#print axioms Sun28.QuadricSieve.auxiliary_shift
#print axioms Sun28.QuadricSieve.literal_diagonal
