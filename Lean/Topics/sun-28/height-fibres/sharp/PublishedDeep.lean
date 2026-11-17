import DeepSector
import CharacterProduct
import TwistSector

namespace Sun28.HeightFibres.Sharp
open Sun28.FiveDescent Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Height
noncomputable section

/-- The three quadratic discriminants are counted formally before applying
the reduced universal obligation. -/
theorem original_iff_published_deep (units : PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (formula : QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Deep :=
  original_iff_deep units pell regulator (conductor_from_characters formula)

theorem sextic_deep_sector (pell : PublishedPell312) (regulator : Regulator35)
    (formula : QuadraticCharacterDiscriminants) {d e : ℤ} (sd : Squarefree d) (se : Squarefree e)
    {x y : ℚ} (nx : x≠0) (ny : y≠0) (point : (e:ℚ)*y^2=sextic d x) (i : Fin 5)
    (covered : let s:=parameter d x
      small ((cutoffProduct:ℝ)*primeProduct (twistPrimes d e)) (numberLog (oldForm i s.num s.den))) :
    logHeight₁ (parameter d x)≤glazerConstant24*(primeProduct (twistPrimes d e):ℝ)^24 := by
  let s:=parameter d x
  obtain ⟨off,hd,he⟩:=inverse sd se nx ny point
  change (∀ i,oldForm i s.num s.den≠0) at off
  change D s.num s.den=d at hd
  change E s.num s.den=e at he
  have cop : Int.gcd s.num (s.den:ℤ)=1 := by simpa [Int.gcd] using s.reduced.gcd_eq_one
  have sup : oddProduct s.num s.den=primeProduct (twistPrimes d e) := by
    rw [oddProduct,oddSupport,support_exact cop off,hd,he]
  have test : small (heightRadical s.num s.den) (numberLog (oldForm i s.num s.den)) := by
    rw [heightRadical,Nat.cast_mul,sup]; exact covered
  have target:=contact_deep pell regulator (conductor_from_characters formula) off i test
  have cmp:=signed_height (show (s.den:ℤ)≠0 by exact_mod_cast s.den_nz) cop
  change logHeight₁ ((s.num:ℚ)/(s.den:ℚ))=pairLogHeight s.num s.den at cmp
  rw [Rat.num_div_den] at cmp
  change logHeight₁ s≤_
  rw [cmp,←sup]
  simpa only [Sun28.MinimalConductors.target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using target


end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.original_iff_published_deep
#print axioms Sun28.HeightFibres.Sharp.sextic_deep_sector
