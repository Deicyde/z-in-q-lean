import PeriodRaySieve
import PeriodLatticeTail
import PeriodLocalDensity

namespace Sun28.PeriodWindows
open ManuscriptV15.Arithmetic Sun28.SieveTail Finset

noncomputable section
open scoped Classical

/-- Transfer from offending Gaussian generators to their actual rational prime
norms: assigning one generator to each norm gives an injection. -/
theorem far_self_bound (K N R : ℕ) (two : 2≤R) :
    ((farSelf K N R).card:ℚ) ≤
      (2*(N.sqrt:ℚ)+1)*(Nat.log 2 (N.sqrt^2+1):ℚ)*((2*(N.sqrt:ℚ)+1)/R+1) := by
  classical
  let S:=farSelf K N R
  have data (x : ↥S) : ∃ z:Gaussian, gaussianNorm z=x.val ∧
      ∃ q : ℕ, q.Prime ∧ R<q ∧ q∣adjacentNorm z true ∧ q∣adjacentNorm z false := by
    obtain ⟨_,q,l,qp,_,inS⟩:=mem_filter.mp x.property
    obtain ⟨_,z,norm,_,plus,minus⟩:=mem_filter.mp inS
    exact ⟨z,norm,q,qp,l,plus,minus⟩
  choose π n bad using data
  let T:=Finset.univ.image π
  have inj:Function.Injective π:=fun a b eq=>Subtype.ext ((n a).symm.trans ((congrArg gaussianNorm eq).trans (n b)))
  have size : T.card=S.card:=by simp [T,Finset.card_image_of_injective _ inj]
  have t:=large_self_count N.sqrt R two T (by
    intro z hz
    obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hz
    have hm:p.val≤N := by
      obtain ⟨base,_⟩:=mem_filter.mp p.property
      have rr:=mem_range.mp (mem_filter.mp base).1
      omega
    have nn : ((π p).1^2+(π p).2^2:ℤ)=(p.val:ℤ) := by
      have en:=congrArg (fun x:ℕ=>(x:ℤ)) (n p)
      simpa only [gaussianNorm,Int.natCast_natAbs,abs_of_nonneg (by positivity : 0≤(π p).1^2+(π p).2^2)] using en
    have ax (a b:ℤ) (eq : a^2+b^2=(p.val:ℤ)) : a∈interval N.sqrt := by
      have lo:a^2≤(N:ℤ):=by nlinarith [show (p.val:ℤ)≤ (N:ℤ) by exact_mod_cast hm,sq_nonneg b]
      have nat:a.natAbs^2≤N:=by
        exact_mod_cast (show ((a.natAbs:ℕ):ℤ)^2≤ (N:ℤ) by rwa [Int.natCast_natAbs,sq_abs])
      have bound:=Nat.le_sqrt.mpr (by simpa [pow_two] using nat)
      apply Finset.mem_Ico.mpr
      omega
    exact ⟨ax _ _ nn,ax _ _ (by rw [add_comm];exact nn)⟩)
    (by intro z hz; obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hz;exact bad x)
  simpa only [size] using t

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.far_self_bound
