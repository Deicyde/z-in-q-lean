import CrossResidues
import ReducedProjection

namespace Sun28.ConeSieve
open Finset Sun28.QuadricSieve Sun28.SinglePrime Sun28.MediumSieve Sun28.ContactFactors
open Sun28.WeightedSelection Sun28.SieveTail Sun28.MixedSieve
noncomputable section
open scoped Classical

def norm1 (x : Coordinates ℤ) := x.1.1^2+x.1.2^2
def value {A : Fin 3 → ℚ} (i k : ↥(shifts A)) (x : Coordinates ℤ) :=
  norm1 x + gap k i * x.2.2^2

theorem value_record {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}
    (a : Candidate A d H Y) (i j k : ↥(shifts A)) :
    value i k (integerPoint a i j) = a.values.value k.val := by
  have norm : norm1 (integerPoint a i j)=(a.values.value i.val:ℤ) := by
    rw [←a.rays.norm i]; change _ = (Int.natAbs (_^2+_^2):ℤ)
    rw [Int.natCast_natAbs,abs_of_nonneg (by positivity)]
    rfl
  rw [value,norm,a.values.equation i.val i.property,a.values.equation k.val k.property]
  dsimp only [gap,integerPoint];ring

def sizeBound (A : Fin 3 → ℚ) (N W : ℕ) := (N+maxCoefficient A*W^2).sqrt

def interval (b : ℕ) := Icc (-(b:ℤ)) (b:ℤ)

def region {A : Fin 3 → ℚ} (i j : ↥(shifts A)) (N W : ℕ) : Finset (Coordinates ℤ) :=
  let D:=interval (sizeBound A N W)
  (((D ×ˢ D) ×ˢ (D ×ˢ D) ×ˢ Icc 1 (W:ℤ))).filter fun x=>
    onCone (gap i j) x ∧ (N:ℤ)<2*(norm1 x-offset (dilation A) i.val*x.2.2^2) ∧
    norm1 x-offset (dilation A) i.val*x.2.2^2 ≤ N

private theorem norm_window {A : Fin 3 → ℚ} {d N W : ℕ} {H Y : ℝ} {a : Candidate A d H Y}
    (ha : a∈box N W) (k : ↥(shifts A)) :
    (a.values.value k.val:ℤ) ≤ (N:ℤ)+maxCoefficient A*(W:ℤ)^2 := by
  obtain ⟨_,u,v⟩:=box_mem ha
  have c:=(le_abs_self (offset (dilation A) k.val)).trans (by
    rw [←Int.natCast_natAbs]
    exact_mod_cast le_sup (f:=fun r : ↥(shifts A)=>(offset (dilation A) r.val).natAbs) (mem_univ k) :
     |offset (dilation A) k.val| ≤ (maxCoefficient A:ℤ))
  rw [a.values.equation k.val k.property]
  exact add_le_add (by exact_mod_cast u) ((mul_le_mul_of_nonneg_right c (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_left v 2) (by positivity)))

theorem record_region {A : Fin 3 → ℚ} {d N W : ℕ} {H Y : ℝ} {a : Candidate A d H Y}
    (ha : a∈box N W) (i j : ↥(shifts A)) : integerPoint a i j∈region i j N W := by
  obtain ⟨low,high,width⟩:=box_mem ha
  have bounds (k : ↥(shifts A)) : a.gaussian k ∈ interval (sizeBound A N W) ×ˢ interval (sizeBound A N W) := by
    have n:=norm_window ha k
    have eq:=(value_record a k j k)
    simp only [value,gap,sub_self,zero_mul,add_zero,norm1,integerPoint] at eq
    have root (m : ℤ) (mh : m^2≤(N:ℤ)+maxCoefficient A*(W:ℤ)^2) : m∈interval (sizeBound A N W) := by
      have a : m.natAbs^2≤N+maxCoefficient A*W^2 := by
        have e : (m.natAbs:ℤ)^2≤(N:ℤ)+maxCoefficient A*(W:ℤ)^2 := by rw [Int.natCast_natAbs,sq_abs];exact mh
        exact_mod_cast e
      have b : m.natAbs ≤ sizeBound A N W := Nat.le_sqrt.mpr (by simpa [pow_two] using a)
      have c : |m|≤(sizeBound A N W:ℤ) := by rw [←Int.natCast_natAbs];exact_mod_cast b
      exact mem_Icc.mpr (abs_le.mp c)
    exact mem_product.mpr ⟨root _ (by nlinarith only [eq,n,sq_nonneg (a.gaussian k).2]),
      root _ (by nlinarith only [eq,n,sq_nonneg (a.gaussian k).1])⟩
  have norm:=(value_record a i j i)
  simp only [value,gap,sub_self,zero_mul,add_zero] at norm
  have h : norm1 (integerPoint a i j)-offset (dilation A) i.val*(integerPoint a i j).2.2^2=(a.u:ℤ) := by
    rw [norm,a.values.equation i.val i.property];dsimp only [integerPoint];ring
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨bounds i,mem_product.mpr ⟨bounds j,mem_Icc.mpr ⟨?_,?_⟩⟩⟩,integer_cone a i j,?_,?_⟩
  · change 1≤(a.v:ℤ);exact_mod_cast (show 1≤a.v from a.positive)
  · change (a.v:ℤ)≤(W:ℤ);exact_mod_cast width
  · rw [h];exact_mod_cast low
  · rw [h];exact_mod_cast high

/-- Actual records survive the sieve of the other quadratic forms on the cone. -/
def badFactors {A : Fin 3 → ℚ} (i : ↥(shifts A)) (P : Finset ℕ) (x : Coordinates ℤ) :=
  P.filter fun p=>reduction p x≠0 ∧ ∃ k : ↥(shifts A),(p:ℤ)∣value i k x

theorem prime_survives {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ} (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (P : Finset ℕ) (pr : ∀ p∈P,p.Prime)
    (large : ∀ p∈P,∀ k : ↥(shifts A),p<a.values.value k.val) :
    badFactors i P (integerPoint a i j)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨pin,_,k,h⟩:=mem_filter.mp hp
  rw [value_record] at h
  have d : p∣a.values.value k.val := by exact_mod_cast h
  rcases (Nat.dvd_prime (a.values.prime k.val k.property)).mp d with eq|eq
  · exact (pr p pin).ne_one eq
  · exact (large p pin k).ne eq

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.value_record
#print axioms Sun28.ConeSieve.record_region
#print axioms Sun28.ConeSieve.prime_survives
