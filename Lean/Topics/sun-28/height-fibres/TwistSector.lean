import FivePencils

/-! The five simultaneous-Pell tests on actual nonzero signed sextic points. -/
namespace Sun28.HeightFibres
open Sun28.FiveDescent Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Height
noncomputable section

/-- A point on the exact signed sextic recovers a unique reduced slope. Any
one small contact on that slope proves the original bound with its literal
large-prime product and its original coefficient. -/
theorem sextic_contact_sector (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) {d e : ℤ} (sd : Squarefree d) (se : Squarefree e)
    {x y : ℚ} (nx : x≠0) (ny : y≠0) (point : (e:ℚ)*y^2=sextic d x) (i : Fin 5)
    (small : let s:=parameter d x
      numberLog (oldForm i s.num s.den)≤((cutoffProduct:ℝ)*primeProduct (twistPrimes d e))^14) :
    logHeight₁ (parameter d x)≤glazerConstant24*(primeProduct (twistPrimes d e):ℝ)^24 := by
  let s:=parameter d x
  obtain ⟨off,hd,he⟩:=inverse sd se nx ny point
  change (∀ i,oldForm i s.num s.den≠0) at off
  change D s.num s.den=d at hd
  change E s.num s.den=e at he
  have cop : Int.gcd s.num (s.den:ℤ)=1 := by simpa [Int.gcd] using s.reduced.gcd_eq_one
  have sup : oddProduct s.num s.den=primeProduct (twistPrimes d e) := by
    rw [oddProduct,oddSupport,support_exact cop off,hd,he]
  have test : numberLog (oldForm i s.num s.den)≤(heightRadical s.num s.den:ℝ)^14 := by
    rw [heightRadical,Nat.cast_mul,sup]; exact small
  have target:=contact_sector pell regulator disc off i test
  have cmp:=signed_height (show (s.den:ℤ)≠0 by exact_mod_cast s.den_nz) cop
  change logHeight₁ ((s.num:ℚ)/(s.den:ℚ))=pairLogHeight s.num s.den at cmp
  rw [Rat.num_div_den] at cmp
  change logHeight₁ s≤_
  rw [cmp,←sup]
  simpa only [Sun28.MinimalConductors.target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using target

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.sextic_contact_sector
