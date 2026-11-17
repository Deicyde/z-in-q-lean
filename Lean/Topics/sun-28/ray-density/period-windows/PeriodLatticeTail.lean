import DiagonalRecords
namespace Sun28.PeriodWindows
open ManuscriptV15.Arithmetic Sun28.SieveTail Sun28.SinglePrime
noncomputable section

/-- Every self-collision past R in a square box of Gaussian coordinates.
No primality of the norm is needed for this upper bound. -/
theorem large_self_count (B R : ℕ) (two : 2≤R) (S : Finset Gaussian)
    (bounds : ∀ z∈S, z.1 ∈ interval B ∧ z.2 ∈ interval B)
    (bad : ∀ z∈S,∃ p : ℕ,p.Prime ∧ R<p ∧ p∣adjacentNorm z true ∧ p∣adjacentNorm z false) :
    (S.card:ℚ) ≤ (2*(B:ℚ)+1)*(Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1) := by
  classical
  let size:ℚ := (Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1)
  have res:=fibre_bound S (interval B) Prod.snd (fun x hx=>(bounds x hx).2) size (by
    intro y hy
    let F:=S.filter (fun z=>z.2=y)
    have inj:Set.InjOn Prod.fst (F:Set Gaussian) := by
      intro a ha b hb eq
      exact Prod.ext eq ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    change (F.card:ℚ) ≤ size
    rw [←Finset.card_image_of_injOn inj]
    have range:=Finset.mem_Ico.mp hy
    have ya:y.natAbs≤B:=by omega
    apply diagonal_fibre B R two y ya
    · intro x mem
      obtain ⟨z,h,rfl⟩:=Finset.mem_image.mp mem
      exact (bounds _ (Finset.mem_filter.mp h).1).1
    · intro x mem
      obtain ⟨z,h,rfl⟩:=Finset.mem_image.mp mem
      obtain ⟨hz,e⟩:=Finset.mem_filter.mp h
      rcases z with ⟨zx,zy⟩
      subst y
      exact bad (zx,zy) hz)
  have n : (interval B).card=2*B+1 := by simp only [interval,Int.card_Ico];omega
  rw [n] at res
  push_cast at res
  simpa only [size,mul_assoc] using res

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.large_self_count
