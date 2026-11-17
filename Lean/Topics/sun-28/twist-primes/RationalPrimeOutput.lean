import NewTwistPrimes

namespace Sun28.TwistPrimes
open PairedClasses PreparedPoles

private theorem local_first : LocalSquareAt 3697 17 := by
  let : Fact (Nat.Prime 3697) := ⟨by norm_num⟩
  apply local_square_of_legendre (by decide)
  apply (legendreSym.eq_one_iff' 3697 (show (17:ZMod 3697)≠0 by decide)).mpr
  exact ⟨940,by decide⟩

private theorem local_second : LocalSquareAt 17 3697 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  apply local_square_of_legendre (by decide)
  apply (legendreSym.eq_one_iff' 17 (show (3697:ZMod 17)≠0 by decide)).mpr
  exact ⟨5,by decide⟩

/-- Prime squarefree output from a rational index. The numerator and
denominator of k are 21 and 4. -/
theorem rational_prime_example : Nat.Prime 3697 ∧ AdmissiblePair 17 3697 ∧
    Family 17 3697 ∧ TwistPoint 17 17 ∧ TwistPoint 17 (17*3697) := by
  have prime : Nat.Prime 3697 := by norm_num
  have bprime : Nat.Prime 17 := by decide
  have fam : Family 17 3697 := ⟨21/4,13/16,by norm_num,by norm_num⟩
  refine ⟨prime,⟨by decide,by decide,bprime.squarefree,prime.squarefree,by decide,by decide,
    by decide,by decide,by decide,?_,?_⟩,fam,fixed_points_of_family (by decide) (by decide) fam⟩
  · intro p pp d
    rw [(Nat.prime_dvd_prime_iff_eq pp prime).mp d]
    exact local_first
  · intro p pp d
    rw [(Nat.prime_dvd_prime_iff_eq pp bprime).mp d]
    exact local_second

end Sun28.TwistPrimes
#print axioms Sun28.TwistPrimes.rational_prime_example
