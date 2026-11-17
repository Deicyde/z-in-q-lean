import ExactDepth
import Mathlib.Algebra.GCDMonoid.Finset

namespace Sun28.ComparisonCRT
noncomputable section

def comparisonPeriod (plus minus κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) : ℕ :=
  Nat.lcm plus (Nat.lcm minus (Nat.lcm κ (T.lcm (fun p=>p^(a p+1)))))

theorem period_positive {plus minus κ : ℕ} {T : Finset ℕ} (a : ℕ→ℕ)
    (hp : 0<plus) (hm : 0<minus) (hk : 0<κ) (prime : ∀ p∈T, Nat.Prime p) :
    0<comparisonPeriod plus minus κ T a := by
  apply Nat.pos_of_ne_zero
  exact Nat.lcm_ne_zero hp.ne' (Nat.lcm_ne_zero hm.ne' (Nat.lcm_ne_zero hk.ne'
    (Finset.lcm_ne_zero_iff.mpr (fun p m=>pow_ne_zero _ (prime p m).ne_zero))))

private theorem modulus_iff {h y : ℤ} {m : ℕ} :
    h ≡ y [ZMOD (m:ℤ)] ↔ m∣(y-h).natAbs := by
  rw [Int.modEq_iff_dvd,←Int.natAbs_dvd_natAbs,Int.natAbs_natCast]

private theorem transfer {m : ℕ} {h y r : ℤ} (base : y ≡ r [ZMOD (m:ℤ)]) :
    h ≡ r [ZMOD (m:ℤ)] ↔ m∣(y-h).natAbs := by
  rw [←modulus_iff]
  exact ⟨fun hx=>hx.trans base.symm,fun hy=>hy.trans base⟩

/-- All solutions have exactly one residue modulo the least common multiple. -/
theorem class_iff {plus minus κ anchor : ℕ} {T : Finset ℕ} {a : ℕ→ℕ} {y h : ℤ}
    (base : Congruences plus minus κ anchor T a y) :
    Congruences plus minus κ anchor T a h ↔
    h ≡ y [ZMOD (comparisonPeriod plus minus κ T a:ℤ)] := by
  rw [modulus_iff,comparisonPeriod,Nat.lcm_dvd_iff,Nat.lcm_dvd_iff,Nat.lcm_dvd_iff,Finset.lcm_dvd_iff]
  have localIff (p : ℕ) (mem : p∈T) :
      h ≡ (p:ℤ)^(a p) [ZMOD (p:ℤ)^(a p+1)] ↔ p^(a p+1) ∣ (y-h).natAbs := by
    have eq : y ≡ (p:ℤ)^(a p) [ZMOD ((p^(a p+1):ℕ):ℤ)] := by
      simpa only [Nat.cast_pow] using base.localResidue p mem
    simpa only [Nat.cast_pow] using (transfer (h:=h) eq)
  constructor
  · intro ok
    exact ⟨(transfer base.plus).1 ok.plus,(transfer base.minus).1 ok.minus,(transfer base.preparation).1 ok.preparation,
      fun p m=>(localIff p m).1 (ok.localResidue p m)⟩
  · rintro ⟨p,m,k,localPart⟩
    exact ⟨(transfer base.plus).2 p,(transfer base.minus).2 m,(transfer base.preparation).2 k,
      fun q hq=>(localIff q hq).2 (localPart q hq)⟩

/-- Instantiates the class at the four arithmetic hypotheses of Sun's CRTa/CRTb. -/
theorem exact_progression (plus minus κ anchor : ℕ) (T : Finset ℕ) (a : ℕ→ℕ)
    (hp : 0<plus) (hm : 0<minus) (hk : 0<κ)
    (prime : ∀ p∈T, Nat.Prime p) (two : 2∈T)
    (gcd : plus.gcd minus=4) (v2p : padicValNat 2 plus=2) (v2m : padicValNat 2 minus=6)
    (localAvoid : ∀ p∈T, p≠2 → ¬p∣plus*minus)
    (kAvoid : ∀ p∈κ.primeFactors, p≠2 → ¬p∣minus)
    (depth : ∀ p∈T,padicValNat p κ≤a p) (dyadic : 6≤a 2) (anchor64 : 64∣anchor) :
    0<comparisonPeriod plus minus κ T a ∧ ∃ offset : ℤ, ∀ h : ℤ,
    Congruences plus minus κ anchor T a h ↔ ∃ k : ℤ,h=offset+(comparisonPeriod plus minus κ T a:ℤ)*k := by
  obtain ⟨y,L,_,all⟩:=comparison_progression plus minus κ anchor T a hp hm hk prime two gcd v2p v2m
    localAvoid kAvoid depth dyadic anchor64
  have base : Congruences plus minus κ anchor T a y := by simpa using all 0
  refine ⟨period_positive a hp hm hk prime,y,fun h=>?_⟩
  rw [class_iff base,Int.modEq_comm,Int.modEq_iff_add_fac]

end
end Sun28.ComparisonCRT
#print axioms Sun28.ComparisonCRT.period_positive
#print axioms Sun28.ComparisonCRT.class_iff
#print axioms Sun28.ComparisonCRT.exact_progression
