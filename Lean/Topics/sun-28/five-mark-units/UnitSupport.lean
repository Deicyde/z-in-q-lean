import HeightTransport
import Mathlib.NumberTheory.Height.NumberField

/-! The unit equation attached to a signed primitive pair. -/
namespace Sun28.FiveMarkUnits
open Sun28.Ordinary Height

def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S,p

def tripleSupport (A B : ℤ) : Finset ℕ :=
  A.natAbs.primeFactors ∪ B.natAbs.primeFactors ∪ (A-B).natAbs.primeFactors

def oddSupport (A B : ℤ) : Finset ℕ := oldContactPrimes oldCutoff A B

def residualSupport (A B : ℤ) : Finset ℕ := tripleSupport A B \ (oldCutoff ∪ oddSupport A B)

def cutoffProduct : ℕ := primeProduct oldCutoff
def oddProduct (A B : ℤ) : ℕ := primeProduct (oddSupport A B)
def residualProduct (A B : ℤ) : ℕ := primeProduct (residualSupport A B)

theorem triple_primes {A B : ℤ} {p : ℕ} (member : p∈tripleSupport A B) : p.Prime := by
  rcases Finset.mem_union.mp member with ab|h
  · rcases Finset.mem_union.mp ab with ha|hb
    · exact Nat.prime_of_mem_primeFactors ha
    · exact Nat.prime_of_mem_primeFactors hb
  · exact Nat.prime_of_mem_primeFactors h

private theorem prod_positive {S : Finset ℕ} (prime : ∀ p∈S,p.Prime) : 0<primeProduct S :=
  Finset.prod_pos fun p hp => (prime p hp).pos

theorem pos_cutoff : 0<cutoffProduct := prod_positive (fun _ hp => (Finset.mem_filter.mp hp).2)
theorem pos_odd (A B : ℤ) : 0<oddProduct A B :=
  prod_positive (fun _ hp => (mem_oldContactPrimes.mp hp).1)

/-- The original projective triple support accounts for every unit of the equation. -/
theorem support_bound (A B : ℤ) : primeProduct (tripleSupport A B) ≤
    cutoffProduct*oddProduct A B*residualProduct A B := by
  let T:=tripleSupport A B
  let C:=oldCutoff
  let O:=oddSupport A B
  let R:=residualSupport A B
  have sub : T ⊆ (C∪O)∪R := by
    intro p hp
    by_cases h : p∈C∪O
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,h⟩)
  have dis : Disjoint C O := by
    apply Finset.disjoint_left.mpr
    exact fun p hp ho => (mem_oldContactPrimes.mp ho).2.1 hp
  have dr : Disjoint (C∪O) R := by
    apply Finset.disjoint_left.mpr
    exact fun p hp hr => (Finset.mem_sdiff.mp hr).2 hp
  have ones (p : ℕ) (hp : p∈(C∪O)∪R) : 1≤p := by
    rcases Finset.mem_union.mp hp with t|r
    · rcases Finset.mem_union.mp t with c|o
      · exact (Finset.mem_filter.mp c).2.one_lt.le
      · exact (mem_oldContactPrimes.mp o).1.one_lt.le
    · exact (triple_primes (Finset.mem_sdiff.mp r).1).one_lt.le
  have h := Finset.prod_le_prod_of_subset_of_one_le (f:=id) sub (fun p hp _ => ones p hp)
  change (∏ p ∈ T,p)≤(∏ p ∈ C,p)*(∏ p ∈ O,p)*(∏ p ∈ R,p)
  simpa only [Finset.prod_union dr,Finset.prod_union dis,id_eq] using h

/-- The elementary rational criterion for membership in Z[1/N_S]^×. -/
def RationalSUnit (S : Finset ℕ) (q : ℚ) : Prop :=
  q≠0 ∧ q.num.natAbs.primeFactors ⊆ S ∧ q.den.primeFactors ⊆ S

/-- von Känel, Integral points on moduli schemes of elliptic curves,
Corollary 7.2, including the stated numerical normalization for both heights. -/
def VonKanel72 : Prop :=
  ∀ (S : Finset ℕ) (_primes : ∀ p∈S,p.Prime) (x y : ℚ), RationalSUnit S x →
    RationalSUnit S y → x+y=1 →
    let n : ℝ := 2^7*(primeProduct S:ℝ)
    logHeight₁ x ≤ (3/2)*n*(Real.log n)^2+65 ∧ logHeight₁ y ≤ (3/2)*n*(Real.log n)^2+65

theorem ratio_unit {A B : ℤ} (na : A≠0) (nb : B≠0) {S : Finset ℕ}
    (num : A.natAbs.primeFactors ⊆ S) (den : B.natAbs.primeFactors ⊆ S) :
    RationalSUnit S ((A:ℚ)/B) := by
  have dn := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd A B)
  have an := Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd A nb)
  simp only [Rat.divInt_eq_div,Int.natAbs_natCast] at dn an
  exact ⟨div_ne_zero (by exact_mod_cast na) (by exact_mod_cast nb),
    (Nat.primeFactors_mono an (Int.natAbs_ne_zero.mpr na)).trans num,
    (Nat.primeFactors_mono dn (Int.natAbs_ne_zero.mpr nb)).trans den⟩

/-- Applied to actual rational numbers. With B negative the same units and equation work. -/
theorem triple_equation {A B : ℤ} (na : A≠0) (nb : B≠0) (diff : A-B≠0) :
    RationalSUnit (tripleSupport A B) ((A:ℚ)/B) ∧
    RationalSUnit (tripleSupport A B) (((B-A:ℤ):ℚ)/B) ∧
    (A:ℚ)/B+((B-A:ℤ):ℚ)/B=1 := by
  have n : B-A≠0 := by omega
  have eqn : (B-A).natAbs=(A-B).natAbs := by rw [←Int.natAbs_neg (B-A)];congr 1;omega
  have den : B.natAbs.primeFactors ⊆ tripleSupport A B :=
    fun p hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp)
  refine ⟨ratio_unit na nb (fun p hp => Finset.mem_union_left _ (Finset.mem_union_left _ hp)) den,
    ratio_unit n nb (fun p hp => Finset.mem_union_right _ (eqn ▸ hp)) den,?_⟩
  push_cast
  field_simp [show (B:ℚ)≠0 by exact_mod_cast nb]
  ring

theorem signed_height {A B : ℤ} (nb : B≠0) (primitive : Int.gcd A B=1) :
    logHeight₁ ((A:ℚ)/B)=pairLogHeight A B := by
  have gcd : B.gcd A=1 := (Int.gcd_comm _ _).trans primitive
  rw [Rat.logHeight₁_eq_log_max,←Rat.divInt_eq_div,Rat.num_divInt,Rat.den_divInt,gcd]
  simp only [nb, ↓reduceIte,Nat.cast_one,Int.ediv_one,Nat.div_one,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nb,one_mul]
  unfold pairLogHeight pairHeight
  simp

theorem off_triple {A B : ℤ} (off : ∀ i, oldForm i A B≠0) : A≠0 ∧ B≠0 ∧ A-B≠0 := by
  exact ⟨by simpa [oldForm] using off 1,by simpa [oldForm] using off 0,by simpa [oldForm] using off 2⟩

end Sun28.FiveMarkUnits
#print axioms Sun28.FiveMarkUnits.support_bound
#print axioms Sun28.FiveMarkUnits.ratio_unit
#print axioms Sun28.FiveMarkUnits.triple_equation
#print axioms Sun28.FiveMarkUnits.signed_height
#print axioms Sun28.FiveMarkUnits.off_triple
