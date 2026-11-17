import Extension

namespace Sun28.HeightExtension
open Sun28.FiveDescent Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres.Sharp Height
noncomputable section

theorem sextic_sparse (finitePell : PublishedFinitePell) (classes : PublishedClassRegulator)
    (formula : QuadraticCharacterDiscriminants) {d e : ℤ} (sd : Squarefree d) (se : Squarefree e)
    {x y : ℚ} (nx : x≠0) (ny : y≠0) (point : (e:ℚ)*y^2=sextic d x) (i : Fin 5)
    (covered : let s:=parameter d x
      (rowPrimes i s.num s.den).card≤4 ∧
        primeProduct (rowPrimes i s.num s.den)≤(cutoffProduct*primeProduct (twistPrimes d e))^4) :
    logHeight₁ (parameter d x)≤glazerConstant24*(primeProduct (twistPrimes d e):ℝ)^24 := by
  let s:=parameter d x
  obtain ⟨off,hd,he⟩:=inverse sd se nx ny point
  change (∀ i,oldForm i s.num s.den≠0) at off
  change D s.num s.den=d at hd
  change E s.num s.den=e at he
  have cop : Int.gcd s.num (s.den:ℤ)=1 := by simpa [Int.gcd] using s.reduced.gcd_eq_one
  have sup : oddProduct s.num s.den=primeProduct (twistPrimes d e) := by
    rw [oddProduct,oddSupport,support_exact cop off,hd,he]
  have test : Sparse i s.num s.den := by
    change _ ∧ _≤(cutoffProduct*oddProduct s.num s.den)^4
    rw [sup];exact covered
  have target:=sparse_height finitePell classes formula cop off i test
  have cmp:=signed_height (show (s.den:ℤ)≠0 by exact_mod_cast s.den_nz) cop
  change logHeight₁ ((s.num:ℚ)/(s.den:ℚ))=pairLogHeight s.num s.den at cmp
  rw [Rat.num_div_den] at cmp
  change logHeight₁ s≤_
  rw [cmp,←sup]
  simpa only [Sun28.MinimalConductors.target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using target

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.sextic_sparse
