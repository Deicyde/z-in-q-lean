import ClassTrace
import CommonPrimes

namespace Sun28.PrimeClasses
open ManuscriptV15.Arithmetic Sun28.CMReduction Sun28.FinitePattern ZInQ.Density

/-- A fixed ray test using only the rational prime and the trace of the fixed curve. -/
def baseRay (p : ℕ) : Prop :=
  p%8=1 ∧ p%7=3 ∧ root p ≡ 9 [ZMOD 16] ∧ root p ≡ 1 [ZMOD 7] ∧
  (p:ℤ) ≡ (root p)^2 [ZMOD 256]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem zero_mod_sixteen {y : ℤ} (h : y^2 ≡ 0 [ZMOD 256]) : y≡0 [ZMOD 16] := by
  have e : (y:ZMod 256)^2=0 := by simpa using (ZMod.intCast_eq_intCast_iff (y^2) 0 256).mpr h
  have test : ∀ x : ZMod 256, x^2=0 → x.val%16=0 := by decide
  have result := test (y:ZMod 256) e
  have rep := ZMod.val_intCast (n:=256) y
  change y%16=0
  omega

private theorem sign_seven {b : ℤ} (hb : b^2 ≡ 2 [ZMOD 7]) :
    b ≡ 3 [ZMOD 7] ∨ -b ≡ 3 [ZMOD 7] := by
  have h : (b:ZMod 7)^2=2 := by simpa using (ZMod.intCast_eq_intCast_iff (b^2) 2 7).mpr hb
  have v : ∀ x : ZMod 7, x^2=2 → x=3 ∨ -x=3 := by decide
  rcases v _ h with pos|neg
  · exact Or.inl ((ZMod.intCast_eq_intCast_iff b 3 7).mp (by simpa using pos))
  · exact Or.inr ((ZMod.intCast_eq_intCast_iff (-b) 3 7).mp (by simpa using neg))

theorem base_ray_iff {p : ℕ} (pp : p.Prime) : baseRay p ↔
    ∃ z : Gaussian, gaussianNorm z=p ∧ gaussianCongruent 16 z (9,0) ∧
      gaussianCongruent 7 z (1,3) := by
  let _ : Fact p.Prime := ⟨pp⟩
  constructor
  · rintro ⟨h8,h7,x16,x7,square⟩
    let x := root p
    obtain ⟨_,b,pair⟩ := root_representation (p:=p) ⟨h8,Or.inl h7⟩
    have b256 : b^2 ≡ 0 [ZMOD 256] := by
      have h := square.sub (Int.ModEq.refl (n:=256) ((root p)^2))
      rw [pair] at h
      convert h using 1 <;> ring
    have b16 := zero_mod_sixteen b256
    have b7 : b^2 ≡ 2 [ZMOD 7] := by
      have pn : (p:ℤ) ≡ 3 [ZMOD 7] := Int.natCast_modEq_iff.mpr h7
      simpa [pair] using pn.sub (x7.pow 2)
    have make (y : ℤ) (norm : (p:ℤ)=x^2+y^2) (h16 : y≡0 [ZMOD 16]) (h7' : y≡3 [ZMOD 7]) :
        ∃ z : Gaussian, gaussianNorm z=p ∧ gaussianCongruent 16 z (9,0) ∧ gaussianCongruent 7 z (1,3) := by
      refine ⟨(x,y),?_,⟨x16,h16⟩,⟨x7,h7'⟩⟩
      exact (Nat.cast_inj (R:=ℤ)).mp ((archive_norm (x,y)).trans norm.symm)
    rcases sign_seven b7 with hb|hb
    · exact make b pair b16 hb
    · exact make (-b) (by simpa [x] using pair) (by simpa only [neg_zero] using b16.neg) hb
  · rintro ⟨z,norm,h16,h7⟩
    have n := archive_norm z
    rw [norm] at n
    have cls := selected_class norm h16 h7
    have mod7 : (p:ℤ) ≡ 3 [ZMOD 7] := by
      rw [n]; exact ((h7.1.pow 2).add (h7.2.pow 2)).trans (by decide)
    have q : (16:ℤ)∣z.2 := Int.modEq_zero_iff_dvd.mp h16.2
    have b256 : z.2^2 ≡ 0 [ZMOD 256] := Int.modEq_zero_iff_dvd.mpr
      (by simpa using pow_dvd_pow_of_dvd q 2)
    refine ⟨cls.1,Int.natCast_modEq_iff.mp mod7,?_,?_,?_⟩
    all_goals rw [root_of_ray pp norm h16 h7]
    · exact h16.1
    · exact h7.1
    · rw [n]; simpa using (Int.ModEq.refl (z.1^2)).add b256

noncomputable def signedOrder (p : ℕ) (s : Bool) : ℤ :=
  (p:ℤ)+1+(if s then 2*root p else -(2*root p))

theorem order_dvd_iff {p : ℕ} (pp : p.Prime) {z : Gaussian} (hz : gaussianNorm z=p)
    (h16 : gaussianCongruent 16 z (9,0)) (h7 : gaussianCongruent 7 z (1,3)) (s : Bool) (q : ℕ) :
    q ∣ adjacentNorm z s ↔ (q:ℤ) ∣ signedOrder p s := by
  rw [←Int.natCast_dvd_natCast,signedOrder,←ray_norms pp hz h16 h7 s]

def rationalPrime (K L p : ℕ) : Prop := p.Prime ∧ baseRay p ∧
  ∀ q : ℕ, q.Prime → q≠2 → q≠7 → q≤L →
    (¬(q:ℤ)∣signedOrder p true) ∧ (q≤K → ¬(q:ℤ)∣signedOrder p false)

theorem common_prime_iff (K L p : ℕ) : commonPrime K L p ↔ rationalPrime K L p := by
  constructor
  · rintro ⟨hp,z,n,h16,h7,hc⟩
    refine ⟨hp,(base_ray_iff hp).mpr ⟨z,n,h16,h7⟩,?_⟩
    intro q hq two seven small
    simpa only [←order_dvd_iff hp n h16 h7] using hc q hq two seven small
  · rintro ⟨hp,base,good⟩
    obtain ⟨z,n,h16,h7⟩ := (base_ray_iff hp).mp base
    refine ⟨hp,z,n,h16,h7,?_⟩
    intro q hq two seven small
    simpa only [order_dvd_iff hp n h16 h7] using good q hq two seven small

end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.base_ray_iff
#print axioms Sun28.PrimeClasses.order_dvd_iff
#print axioms Sun28.PrimeClasses.common_prime_iff
