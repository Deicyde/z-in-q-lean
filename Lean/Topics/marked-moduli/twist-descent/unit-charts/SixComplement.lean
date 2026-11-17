import SixTwistUnits
import ContactSupport

/-! Complementary triples of the six branch rows, and the two earlier cubic coordinates. -/
namespace ZInQBlueprint.SixUnitCharts
open Sun28.FiveMarkUnits ZInQ ZInQBlueprint.OddSupport ZInQBlueprint.TwistDescent
open UniqueFactorizationMonoid

def rowSupport (U : Finset (Fin 6)) (a b : ℤ) : Finset ℕ :=
  fixedPrimes ∪ U.biUnion (fun i => formPrimes i a b)

theorem complementary_product (U : Finset (Fin 6)) {a b : ℤ} (primitive : Int.gcd a b=1) :
    primeProduct (rowSupport U a b)*primeProduct (rowSupport (Finset.univ\U) a b) =
      6*primeProduct (rowSupport Finset.univ a b) := by
  let S := rowSupport U a b
  let T := rowSupport (Finset.univ\U) a b
  have meet : S∩T=fixedPrimes := by
    ext p
    constructor
    · intro h
      obtain ⟨hs,ht⟩ := Finset.mem_inter.mp h
      by_contra away
      obtain ⟨i,hi,fi⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp hs).resolve_left away)
      obtain ⟨j,hj,fj⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp ht).resolve_left away)
      exact (Finset.mem_sdiff.mp hj).2 ((unique_form primitive away fi fj) ▸ hi)
    · intro h
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h,Finset.mem_union_left _ h⟩
  have join : S∪T=rowSupport Finset.univ a b := by
    ext p
    simp only [S,T,rowSupport,Finset.mem_union,Finset.mem_biUnion,Finset.mem_sdiff,Finset.mem_univ,true_and]
    grind
  have h := Finset.prod_union_inter (s₁:=S) (s₂:=T) (f:=fun p : ℕ=>p)
  rw [join,meet] at h
  have six : primeProduct fixedPrimes=6 := by decide
  change primeProduct S*primeProduct T=_
  change primeProduct (rowSupport Finset.univ a b)*primeProduct fixedPrimes=primeProduct S*primeProduct T at h
  rw [←h,six,mul_comm]

theorem triple_rows (i j k : Fin 6) (a b : ℤ) :
    primeProduct (rowSupport {i,j,k} a b)=conductor i j k a b := by
  simp only [rowSupport,conductor,triplePrimes,Finset.biUnion_insert,Finset.singleton_biUnion,Finset.union_assoc]

/-- A single inequality in the full six-row support suffices on every twist. -/
theorem pooled_height (published : PublishedCorollary72) {d : ℤ} {x y : ℚ}
    (hd : d≠0) (hy : y≠0) (point : 30*(d:ℚ)*y^2=quintic x)
    (small : 6*primeProduct (rowSupport Finset.univ x.num x.den)≤(100*d.natAbs)^46) :
    ratHeight x≤10^54*(d.natAbs:ℝ)^24 := by
  let U : Finset (Fin 6) := {0,2,3}
  have comp : Finset.univ\U=({1,4,5}:Finset (Fin 6)) := by decide
  have h := complementary_product U (a:=x.num) (b:=(x.den:ℤ)) (by simpa [Int.gcd] using x.reduced)
  rw [comp] at h
  dsimp only [U] at h
  rw [triple_rows,triple_rows] at h
  let T := (100*d.natAbs)^23
  have prod : conductor 0 2 3 x.num x.den*conductor 1 4 5 x.num x.den≤T*T :=
    h.le.trans (by convert small using 1; ring)
  have off := twist_rows hd hy point
  by_cases b : conductor 0 2 3 x.num x.den ≤ T
  · exact chart_height published (Int.natAbs_pos.mpr hd) (by decide : (0:Fin 6)≠2)
      (by decide : (0:Fin 6)≠3) (by decide : (2:Fin 6)≠3) off b
  · have other : conductor 1 4 5 x.num x.den≤T := by
      by_contra! fail
      exact (not_lt_of_ge prod) (Nat.mul_lt_mul_of_lt_of_lt (lt_of_not_ge b) fail)
    exact chart_height published (Int.natAbs_pos.mpr hd) (by decide : (1:Fin 6)≠4)
      (by decide : (1:Fin 6)≠5) (by decide : (4:Fin 6)≠5) off other

private theorem primes_six : (6:ℕ).primeFactors=fixedPrimes := by
  rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide) (by decide),Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
  decide

/-- The numeric conductor of a triple is exactly the radical including 2 and 3. -/
theorem conductor_radical (i j k : Fin 6) {a b : ℤ} (off : ∀ n,row n a b≠0) :
    conductor i j k a b=radical (6*(row i a b*row j a b*row k a b).natAbs) := by
  have six : (6:ℕ).primeFactors=fixedPrimes := primes_six
  rw [Nat.radical_eq_prod_primeFactors]
  simp only [conductor,primeProduct,triplePrimes,formPrimes,Int.natAbs_mul]
  rw [Nat.primeFactors_mul (by decide) (by positivity [Int.natAbs_pos.mpr (off i),Int.natAbs_pos.mpr (off j),Int.natAbs_pos.mpr (off k)])]
  simp only [Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (off i)) (Int.natAbs_ne_zero.mpr (off j)),
    Nat.primeFactors_mul (mul_ne_zero (Int.natAbs_ne_zero.mpr (off i)) (Int.natAbs_ne_zero.mpr (off j))) (Int.natAbs_ne_zero.mpr (off k)),six]

private theorem scaled_radical {k w : ℤ} (hk : k=1 ∨ k=2) (nz : w≠0) :
    radical (6*(k^3*w).natAbs)=radical (6*w.natAbs) := by
  rcases hk with rfl|rfl
  · simp
  · have six : (6:ℕ).primeFactors=({2,3}:Finset ℕ) := primes_six
    have eight : (8:ℕ).primeFactors=({2}:Finset ℕ) := by rw [show (8:ℕ)=2^3 by decide,Nat.primeFactors_pow _ (by decide),Nat.prime_two.primeFactors]
    rw [Int.natAbs_mul,show ((2:ℤ)^3).natAbs=8 by decide]
    rw [Nat.radical_eq_prod_primeFactors,Nat.radical_eq_prod_primeFactors,
      Nat.primeFactors_mul (by decide) (mul_ne_zero (by decide : (8:ℕ)≠0) (Int.natAbs_ne_zero.mpr nz)),
      Nat.primeFactors_mul (by decide) (Int.natAbs_ne_zero.mpr nz),
      Nat.primeFactors_mul (by decide) (Int.natAbs_ne_zero.mpr nz),six,eight]
    congr 1
    ext p
    simp

/-- The two pure triples recover the supports of the old primitive Mordell construction. -/
theorem cubic_conductors {a b k P Q : ℤ} (off : ∀ n,row n a b≠0)
    (hk : k=1 ∨ k=2) (pn : P≠0) (qn : Q≠0)
    (hP : k^3*P=realCubic a b) (hQ : k^3*Q=imaginaryCubic a b) :
    conductor 1 4 5 a b=radical (6*P.natAbs) ∧ conductor 0 2 3 a b=radical (6*Q.natAbs) := by
  have realprod : row 1 a b*row 4 a b*row 5 a b=realCubic a b := by simp [row,coeffA,coeffB,realCubic]; ring
  have imagprod : row 0 a b*row 2 a b*row 3 a b=imaginaryCubic a b := by simp [row,coeffA,coeffB,imaginaryCubic]; ring
  rw [conductor_radical _ _ _ off,conductor_radical _ _ _ off,realprod,imagprod,←hP,←hQ,
    scaled_radical hk pn,scaled_radical hk qn]
  exact ⟨rfl,rfl⟩

theorem old_sector_included {a b k P Q : ℤ} {D : ℕ} (hd : 0<D) (off : ∀ n,row n a b≠0)
    (hk : k=1 ∨ k=2) (pn : P≠0) (qn : Q≠0)
    (hP : k^3*P=realCubic a b) (hQ : k^3*Q=imaginaryCubic a b)
    (old : min (radical P.natAbs) (radical Q.natAbs)≤30*D^11) :
    conductor 1 4 5 a b≤(100*D)^23 ∨ conductor 0 2 3 a b≤(100*D)^23 := by
  obtain ⟨p,q⟩ := cubic_conductors off hk pn qn hP hQ
  have side (w : ℕ) (small : radical w≤30*D^11) : radical (6*w)≤(100*D)^23 := by
    have six : radical (6:ℕ)=6 := by rw [Nat.radical_eq_prod_primeFactors,primes_six]; decide
    calc
      radical (6*w) ≤ radical 6 * radical w :=
        Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos _) (Nat.radical_pos _)) radical_mul_dvd
      _ ≤ 6*(30*D^11) := by rw [six]; exact Nat.mul_le_mul_left 6 small
      _ ≤ 100^23*D^23 := by
        rw [←mul_assoc]
        exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hd (by decide))
      _ = _ := (Nat.mul_pow ..).symm
  rw [p,q]
  exact (min_le_iff.mp old).imp (side _) (side _)

end ZInQBlueprint.SixUnitCharts
#print axioms ZInQBlueprint.SixUnitCharts.complementary_product
#print axioms ZInQBlueprint.SixUnitCharts.pooled_height
#print axioms ZInQBlueprint.SixUnitCharts.conductor_radical
#print axioms ZInQBlueprint.SixUnitCharts.cubic_conductors
#print axioms ZInQBlueprint.SixUnitCharts.old_sector_included
