import CubeFactors
import PrimeTail

namespace Sun28.ArtinCube
open Finset Sun28.SinglePrime
open scoped Classical
noncomputable section

/-- Prime divisors of a fixed positive step have a bounded aggregate contribution. -/
theorem exceptional_sum (T : Finset ℕ) (v q : ℕ) (large : 2 ≤ v) (qn : 0 < q)
    (good : ∀ p ∈ T, v < p ∧ p.Prime ∧ p ∣ q) :
    (∑ p ∈ T, 1/(p:ℝ)) ≤ Real.log q/((v:ℝ)*Real.log v) := by
  let prod := ∏ p ∈ T,p
  have sub : T ⊆ q.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨(good p hp).2.1,(good p hp).2.2,qn.ne'⟩
  have dvd : prod ∣ q := (prod_dvd_prod_of_subset _ _ (fun n : ℕ => n) sub).trans (Nat.prod_primeFactors_dvd q)
  have prodpos : 0<prod := prod_pos (fun p hp => (good p hp).2.1.pos)
  have logsum : (∑ p ∈ T,Real.log (p:ℝ)) ≤ Real.log q := by
    have lb := Real.log_le_log (by exact_mod_cast prodpos : 0<(prod:ℝ))
          (by exact_mod_cast Nat.le_of_dvd qn dvd : (prod:ℝ)≤q)
    simpa only [prod,Nat.cast_prod,Real.log_prod (s:=T) (f:=fun p : ℕ => (p:ℝ)) (fun p hp => (by exact_mod_cast (good p hp).2.1.ne_zero : (p:ℝ)≠0))] using lb
  have vp : 0 < (v:ℝ) := by exact_mod_cast (show 0<v by omega)
  have vl : 0 < Real.log (v:ℝ) := Real.log_pos (by exact_mod_cast (show 1<v by omega))
  apply (le_div_iff₀ (mul_pos vp vl)).mpr
  rw [sum_mul]
  apply le_trans (sum_le_sum (g:=fun p : ℕ => Real.log (p:ℝ)) ?_) logsum
  intro p hp
  have high : (v:ℝ)≤p := by exact_mod_cast (good p hp).1.le
  have pp := vp.trans_le high
  have comp := mul_le_mul_of_nonneg_right high vl.le
  apply le_trans _ (Real.log_le_log vp high)
  rw [one_div_mul_eq_div,div_le_iff₀ pp]; linarith

/-- Local factors for the linear forms attached to any set of cube vertices.
The shifts can vary independently with the vertices and with the prime. -/
def localFactor {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (Finset ι))
    (q : ℕ) (b : (p : ℕ) → Finset ι → ZMod p) (p : ℕ) : ℝ :=
  if h : p.Prime then
    let _ : Fact p.Prime := ⟨h⟩
    factor S (q:ZMod p) (b p)
  else 1

/-- A uniform bound for every finite product, at the level of the sum of the
absolute deviations. When log(q)≤Cv its right hand side tends to zero. -/
theorem local_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (Finset ι))
    (v R q : ℕ) (b : (p : ℕ) → Finset ι → ZMod p) (large : 2≤v)
    (cap : 2*S.card ≤ v) (qn : 0<q) :
    (∑ p ∈ places v R, |localFactor S q b p - 1|) ≤
      (2*(S.card:ℝ)^2*(4*Real.log 4)+2*S.card*Real.log q)/((v:ℝ)*Real.log v) := by
  let P := places v R
  let B := P.filter (fun p => p ∣ q)
  have point (p : ℕ) (hp : p ∈ P) : |localFactor S q b p - 1| ≤
      2*(S.card:ℝ)^2*(1/(p:ℝ)^2)+(if p ∣ q then 2*(S.card:ℝ)*(1/(p:ℝ)) else 0) := by
    have prime := (mem_places.mp hp).2.2
    let _ : Fact p.Prime := ⟨prime⟩
    have enough := cap.trans (mem_places.mp hp).1.le
    rw [localFactor,dite_eq_left prime]
    by_cases dd : p ∣ q
    · rw [ite_eq_left dd];apply (factor_any S (q:ZMod p) (b p) enough).trans
      have bound : 0 ≤ 2*(S.card:ℝ)^2*(1/(p:ℝ)^2) := by positivity
      linarith only [bound,show (2:ℝ)*(S.card/p)=2*S.card*(1/(p:ℝ)) by ring]
    · rw [ite_eq_right dd,add_zero]
      have nz : (q:ZMod p) ≠ 0 := fun eq => dd ((ZMod.natCast_eq_zero_iff ..).mp eq)
      exact (factor_good S (q:ZMod p) nz (b p) enough).trans_eq (by ring)
  have ex := exceptional_sum B v q large qn (fun p hp =>
    ⟨(mem_places.mp (mem_filter.mp hp).1).1,(mem_places.mp (mem_filter.mp hp).1).2.2,(mem_filter.mp hp).2⟩)
  calc
    _ ≤ _ := sum_le_sum point
    _ = 2*(S.card:ℝ)^2*(∑ p ∈ P,1/(p:ℝ)^2)+2*S.card*(∑ p ∈ B,1/(p:ℝ)) := by
      rw [sum_add_distrib, mul_sum, mul_sum, sum_filter]
    _ ≤ 2*(S.card:ℝ)^2*((4*Real.log 4)/((v:ℝ)*Real.log v))+2*S.card*(Real.log q/((v:ℝ)*Real.log v)) :=
      add_le_add (mul_le_mul_of_nonneg_left (Sun28.PrimeMass.reciprocal_prime_tail v R large) (by positivity))
        (mul_le_mul_of_nonneg_left ex (by positivity))
    _ = _ := by ring

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.exceptional_sum
#print axioms Sun28.ArtinCube.local_sum
