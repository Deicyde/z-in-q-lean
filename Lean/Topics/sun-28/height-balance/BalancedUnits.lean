import SharpMixed

/-! A rational unit equation from the shared square class on three auxiliary rows. -/
namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors
noncomputable section

structure FourRows where
  center : Fin 5
  a : Fin 5
  b : Fin 5
  c : Fin 5
  ia : center ≠ a
  ib : center ≠ b
  ic : center ≠ c
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

namespace FourRows
def weightA (R : FourRows) := det R.center R.b * det R.center R.c
def weightB (R : FourRows) := det R.center R.a * det R.center R.c
def weightC (R : FourRows) := det R.center R.a * det R.center R.b

/-- The same signed square class on the three scaled integer forms. -/
structure Balance (R : FourRows) (A B d u v w : ℤ) : Prop where
  first : R.weightA * oldForm R.a A B = d*u^2
  second : R.weightB * oldForm R.b A B = d*v^2
  third : R.weightC * oldForm R.c A B = d*w^2

def primes (R : FourRows) (A B : ℤ) := core ∪ formPrimes R.center A B

theorem primes_prime (R : FourRows) (A B : ℤ) {p : ℕ} (hp : p∈R.primes A B) : p.Prime := by
  rcases Finset.mem_union.mp hp with h|h <;> exact Nat.prime_of_mem_primeFactors h

private theorem form_diff (i a b : Fin 5) (A B : ℤ) :
    det i b * oldForm a A B - det i a * oldForm b A B = det a b * oldForm i A B := by
  simp only [form_coeff,det]
  ring

theorem differences (R : FourRows) {A B d u v w : ℤ} (h : R.Balance A B d u v w) :
    d*(u^2-v^2)=(det R.center R.c*det R.a R.b)*oldForm R.center A B ∧
    d*(u^2-w^2)=(det R.center R.b*det R.a R.c)*oldForm R.center A B ∧
    d*(v^2-w^2)=(det R.center R.a*det R.b R.c)*oldForm R.center A B := by
  have x:=h.first
  have y:=h.second
  have z:=h.third
  unfold weightA at x; unfold weightB at y; unfold weightC at z
  refine ⟨?_,?_,?_⟩
  · linear_combination -x + y + det R.center R.c * form_diff R.center R.a R.b A B
  · linear_combination -x + z + det R.center R.b * form_diff R.center R.a R.c A B
  · linear_combination -y + z + det R.center R.a * form_diff R.center R.b R.c A B

private theorem factors {d u v J F : ℤ} (j : J≠0) (f : F≠0)
    (identity : d * (u^2-v^2)=J*F) {S : Finset ℕ}
    (hs : J.natAbs.primeFactors ⊆ S) (hf : F.natAbs.primeFactors ⊆ S) :
    (u+v≠0 ∧ (u+v).natAbs.primeFactors⊆S) ∧ (u-v≠0 ∧ (u-v).natAbs.primeFactors⊆S) := by
  have nz := mul_ne_zero j f
  have major : (J*F).natAbs.primeFactors⊆S := by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr j) (Int.natAbs_ne_zero.mpr f)]
    exact Finset.union_subset hs hf
  have lift (x y : ℤ) (e : J*F=x*y) : x≠0 ∧ x.natAbs.primeFactors⊆S := by
    refine ⟨fun h=>nz (by simp [e,h]), ?_⟩
    exact (Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr ⟨y,e⟩) (Int.natAbs_ne_zero.mpr nz)).trans major
  exact ⟨lift (u+v) (d*(u-v)) (by linear_combination -identity),
    lift (u-v) (d*(u+v)) (by linear_combination -identity)⟩

def plus (u v w : ℤ) : ℚ := ((u+v:ℤ):ℚ)/((u+w:ℤ):ℚ)
def minus (u v w : ℤ) : ℚ := ((u-v:ℤ):ℚ)/((u+w:ℤ):ℚ)

/-- Two three-term equations over the localization of one row and 210. -/
theorem units (R : FourRows) {A B d u v w : ℤ} (off : ∀ i,oldForm i A B≠0)
    (bal : R.Balance A B d u v w) :
    (RationalSUnit (R.primes A B) (plus u v w) ∧ RationalSUnit (R.primes A B) (1-plus u v w)) ∧
    (RationalSUnit (R.primes A B) (minus u v w) ∧ RationalSUnit (R.primes A B) (1-minus u v w)) := by
  let S:=R.primes A B
  have f : (oldForm R.center A B).natAbs.primeFactors⊆S := Finset.subset_union_right
  have minors (x y z t : Fin 5) (xy : x≠y) (zt : z≠t) :
      (det x y*det z t).natAbs.primeFactors⊆S := by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne xy)) (Int.natAbs_ne_zero.mpr (det_ne zt))]
    exact (Finset.union_subset (minor_support x y) (minor_support z t)).trans Finset.subset_union_left
  obtain ⟨h₁,h₂,h₃⟩:=R.differences bal
  obtain ⟨p,m⟩:=factors (mul_ne_zero (det_ne R.ic) (det_ne R.ab)) (off _) h₁ (minors _ _ _ _ R.ic R.ab) f
  obtain ⟨q,_⟩:=factors (mul_ne_zero (det_ne R.ib) (det_ne R.ac)) (off _) h₂ (minors _ _ _ _ R.ib R.ac) f
  obtain ⟨e,l⟩:=factors (mul_ne_zero (det_ne R.ia) (det_ne R.bc)) (off _) h₃ (minors _ _ _ _ R.ia R.bc) f
  have nq : ((u+w:ℤ):ℚ)≠0:=by exact_mod_cast q.1
  have ep : 1-plus u v w=((- (v-w):ℤ):ℚ)/((u+w:ℤ):ℚ) := by
    unfold plus; field_simp [nq]; push_cast; ring
  have em : 1-minus u v w=((v+w:ℤ):ℚ)/((u+w:ℤ):ℚ) := by
    unfold minus; field_simp [nq]; push_cast; ring
  exact ⟨⟨ratio_unit p.1 q.1 p.2 q.2,ep ▸ ratio_unit (neg_ne_zero.mpr l.1) q.1
    (by simpa only [Int.natAbs_neg] using l.2) q.2⟩,
    ⟨ratio_unit m.1 q.1 m.2 q.2, em ▸ ratio_unit e.1 q.1 e.2 q.2⟩⟩

end FourRows
end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.FourRows.primes_prime
#print axioms Sun28.HeightBalance.FourRows.differences
#print axioms Sun28.HeightBalance.FourRows.units
