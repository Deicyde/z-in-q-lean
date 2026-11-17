import DiagonalRecords

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection
open ManuscriptV15.Arithmetic
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- Diagonal obstruction at a fixed denominator and shift on the actual numerical records. -/
theorem diagonal_records (boxes : CountingBoxes A d H Y) (N V R : ℕ) (two : 2≤R) (i : ↥(shifts A)) :
    let B := Nat.sqrt (N+(offset (dilation A) i.val).natAbs*V^2)
    ((pairRecords boxes N V R i i).card:ℚ) ≤
      (2*(B:ℚ)+1)*(Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1) := by
  classical
  let B := Nat.sqrt (N+(offset (dilation A) i.val).natAbs*V^2)
  let S := pairRecords boxes N V R i i
  have bounds (a : Record A d H Y) (ha : a∈S) :
      |(a.gaussian i).1|≤(B:ℤ) ∧ |(a.gaussian i).2|≤(B:ℤ) := by
    have ha' := Finset.mem_filter.mp ha
    exact coordinates a i N V _ (boxes.inBox N a ha'.1).2.1 ha'.2.1 le_rfl
  have incl (z : ℤ) (hz : |z|≤(B:ℤ)) : z∈interval B :=
    Finset.mem_Ico.mpr ⟨(abs_le.mp hz).1,by have h:=(abs_le.mp hz).2;omega⟩
  let size := (Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1)
  have bd := fibre_bound S (interval B) (fun a=> (a.gaussian i).2)
    (fun a ha=>incl _ (bounds a ha).2) size (by
      intro y hy
      let U := S.filter (fun a=> (a.gaussian i).2=y)
      let f := fun a : Record A d H Y=> (a.gaussian i).1
      have inj : Set.InjOn f U := by
        intro a ha b hb e
        obtain ⟨as,ay⟩:=Finset.mem_filter.mp ha
        obtain ⟨bs,by'⟩:=Finset.mem_filter.mp hb
        obtain ⟨ar,av,_⟩:=Finset.mem_filter.mp as
        obtain ⟨br,bv,_⟩:=Finset.mem_filter.mp bs
        have val:=congrArg gaussianNorm (Prod.ext e (ay.trans by'.symm) : a.gaussian i=b.gaussian i)
        rw [a.rays.norm i,b.rays.norm i] at val
        have q := congrArg (fun t : ℕ=>(t:ℤ)) val
        rw [a.values.equation i.val i.property,b.values.equation i.val i.property,av,bv] at q
        exact boxes.uniquePair N a ar b br (by omega) (av.trans bv.symm)
      change (U.card:ℚ)≤ size
      rw [←Finset.card_image_of_injOn inj]
      have z:=Finset.mem_Ico.mp hy
      have ay : |y|≤(B:ℤ) := abs_le.mpr ⟨z.1,by omega⟩
      have yn : y.natAbs≤B := by exact_mod_cast (show (y.natAbs:ℤ)≤(B:ℤ) by rwa [Int.natCast_natAbs])
      apply diagonal_fibre B R two y yn
      · intro x hx
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
        exact incl _ (bounds a (Finset.mem_filter.mp ha).1).1
      · intro x hx
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
        obtain ⟨as,ay'⟩:=Finset.mem_filter.mp ha
        rw [←ay'];exact (Finset.mem_filter.mp as).2.2)
  have card : ((interval B).card:ℚ)=2*(B:ℚ)+1 := by
    have n : (interval B).card=2*B+1 := by simp only [interval,Int.card_Ico];omega
    exact_mod_cast n
  dsimp only
  rw [card] at bd
  simpa only [size,mul_assoc] using bd
end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.diagonal_records
