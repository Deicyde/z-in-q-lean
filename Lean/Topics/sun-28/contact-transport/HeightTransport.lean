import ProjectiveContacts
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Height transport with no coordinate exceptions and an explicit finite-prime constant. -/
namespace Sun28.Ordinary
open scoped BigOperators

/-- Multiplicative projective height on a primitive pair, with integral coordinates. -/
def pairHeight (U V : ℤ) : ℤ := max |U| |V|

theorem pairHeight_phi (U V : ℤ) : pairHeight U V≤3*pairHeight (2*U+V) U := by
  let H := pairHeight (2*U+V) U
  have a : |2*U+V|≤H := le_max_left _ _
  have b : |U|≤H := le_max_right _ _
  have pos : 0≤H := (abs_nonneg U).trans b
  apply max_le
  · change |U|≤3*H
    omega
  · change |V|≤3*H
    have hu := le_abs_self U
    have hl := neg_abs_le U
    have au := le_abs_self (2*U+V)
    have al := neg_abs_le (2*U+V)
    rw [abs_le]
    constructor <;> omega

/-- The multiplicative factor 3 is exact, already at (-1:3). -/
theorem pairHeight_phi_sharp : pairHeight (-1) 3=3*pairHeight (2*(-1)+3) (-1) := by
  norm_num [pairHeight]

theorem pairHeight_pos (U V : ℤ) (nonzero : U≠0 ∨ V≠0) : 0<pairHeight U V := by
  rcases nonzero with h|h
  · exact (abs_pos.mpr h).trans_le (le_max_left _ _)
  · exact (abs_pos.mpr h).trans_le (le_max_right _ _)

noncomputable def pairLogHeight (U V : ℤ) : ℝ := Real.log (pairHeight U V:ℝ)

theorem logHeight_phi (U V : ℤ) (nonzero : U≠0 ∨ V≠0) :
    pairLogHeight U V≤Real.log 3+pairLogHeight (2*U+V) U := by
  have h : 0 < (pairHeight U V:ℝ) := by exact_mod_cast pairHeight_pos U V nonzero
  have h' : (pairHeight U V:ℝ)≤3*(pairHeight (2*U+V) U:ℝ) := by exact_mod_cast pairHeight_phi U V
  have pos : 0<(pairHeight (2*U+V) U:ℝ) := by linarith
  unfold pairLogHeight
  rw [←Real.log_mul (by norm_num) pos.ne']
  exact Real.log_le_log h h'

/-- Exactly the additional primes the enlarged exceptional set can remove. -/
def extraPrimes (S E : Finset ℕ) : Finset ℕ := (E \ S).filter Nat.Prime

def contactRadical (S : Finset ℕ) (t : ℚ) : ℕ := ∏ p ∈ contactPrimes S t, p

theorem radical_pos (S : Finset ℕ) (t : ℚ) : 0<contactRadical S t := by
  exact Finset.prod_pos (fun p h => (mem_contactPrimes.mp h).1.pos)

/-- Enlarging a cutoff costs at most the product of extra prime factors, each once. -/
theorem radical_enlargement (S E : Finset ℕ) (t : ℚ) :
    contactRadical S t ≤ (∏ p ∈ extraPrimes S E,p)*contactRadical E t := by
  classical
  have subset : contactPrimes S t ⊆ extraPrimes S E ∪ contactPrimes E t := by
    intro p hp
    obtain ⟨prime,away,contact⟩ := mem_contactPrimes.mp hp
    by_cases inside : p∈E
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨inside,away⟩,prime⟩)
    · exact Finset.mem_union_right _ (mem_contactPrimes.mpr ⟨prime,inside,contact⟩)
  have disjoint : Disjoint (extraPrimes S E) (contactPrimes E t) := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    exact (mem_contactPrimes.mp he).2.1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have pos (p : ℕ) (hp : p∈extraPrimes S E ∪ contactPrimes E t) : 1≤p := by
    rcases Finset.mem_union.mp hp with e|c
    · exact (Finset.mem_filter.mp e).2.one_lt.le
    · exact (mem_contactPrimes.mp c).1.one_lt.le
  have h := Finset.prod_le_prod_of_subset_of_one_le (f:=fun p:ℕ => p) subset (fun p hp _ => pos p hp)
  simpa only [Finset.prod_union disjoint,contactRadical] using h

/-- The original five-mark estimate, stated on every primitive representative
off the five original divisors. -/
def OriginalFiveHeight (C : ℝ) (S : Finset ℕ) : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i, oldForm i A B≠0) →
    pairLogHeight A B≤C*(∏ p ∈ oldContactPrimes S A B,(p:ℝ))^24

private theorem off_old_marks (t : ℚ) (off : t∉marks) : ∀ i, oldForm i (2*t.num+t.den) t.num≠0 := by
  intro i
  have distinct : t≠transportedMark i := fun e => off (e ▸ (marks_image _).mpr ⟨i,rfl⟩)
  have c : contactForm t (transportedMark i)≠0 := by
    intro z
    apply distinct
    have eq : t.num*((transportedMark i).den:ℤ)=(transportedMark i).num*(t.den:ℤ) := by
      exact sub_eq_zero.mp z
    rw [←Rat.num_div_den t,←Rat.num_div_den (transportedMark i)]
    apply (div_eq_div_iff (by exact_mod_cast t.den_nz) (by exact_mod_cast (transportedMark i).den_nz)).mpr
    exact_mod_cast eq
  rw [old_form_pullback,reduced_forms]
  split_ifs <;> simpa using c

theorem finite_contact_height24 {C : ℝ} (cpos : 0≤C) (S E : Finset ℕ)
    (upstream : OriginalFiveHeight C S) (t : ℚ) (off : t∉marks) :
    pairLogHeight t.num t.den ≤
      (C*(∏ p ∈ extraPrimes S E,(p:ℝ))^24 + Real.log 3)*(contactRadical E t:ℝ)^24 := by
  have primitive : Int.gcd t.num (t.den:ℤ)=1 := by simpa [Int.gcd] using t.reduced.gcd_eq_one
  have source := upstream (2*t.num+t.den) t.num ((primitive_phi _ _).trans primitive) (off_old_marks t off)
  rw [transported_contact_primes] at source
  have source' : pairLogHeight (2*t.num+t.den) t.num ≤ C*(contactRadical S t:ℝ)^24 := by
    simpa [contactRadical,Nat.cast_prod] using source
  have extra : (contactRadical S t:ℝ) ≤ (∏ p ∈ extraPrimes S E,(p:ℝ))*(contactRadical E t:ℝ) := by
    rw [←Nat.cast_prod]
    exact_mod_cast radical_enlargement S E t
  have rpos : 1≤(contactRadical E t:ℝ) := by exact_mod_cast radical_pos E t
  have rpow : 1≤(contactRadical E t:ℝ)^24 := one_le_pow₀ rpos
  have loss := mul_le_mul_of_nonneg_left rpow (Real.log_nonneg (by norm_num : (1:ℝ)≤3))
  have hp := pow_le_pow_left₀ (by positivity : 0≤(contactRadical S t:ℝ)) extra 24
  rw [mul_pow] at hp
  have source'' := source'.trans (mul_le_mul_of_nonneg_left hp cpos)
  have change := logHeight_phi t.num t.den (Or.inr (by exact_mod_cast t.den_nz))
  nlinarith

/-- The precise cutoff in the form of the five-contact estimate used by Sun. -/
def oldCutoff : Finset ℕ := (Finset.range 76177).filter Nat.Prime

theorem finite_contact_height_at_cutoff {C : ℝ} (cpos : 0≤C) (E : Finset ℕ)
    (upstream : OriginalFiveHeight C oldCutoff) (t : ℚ) (off : t∉marks) :
    pairLogHeight t.num t.den ≤
      (C*(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24+Real.log 3)*(contactRadical E t:ℝ)^24 :=
  finite_contact_height24 cpos oldCutoff E upstream t off

/-- The constant H_* displayed in the archived Glazer five-contact theorem. -/
noncomputable def glazerConstant24 : ℝ :=
  2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24+128

theorem glazer_five_height_transported (E : Finset ℕ)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff) (t : ℚ) (off : t∉marks) :
    pairLogHeight t.num t.den ≤
      (glazerConstant24*(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24+Real.log 3)*(contactRadical E t:ℝ)^24 := by
  apply finite_contact_height_at_cutoff _ E upstream t off
  unfold glazerConstant24
  positivity

end Sun28.Ordinary
#print axioms Sun28.Ordinary.pairHeight_phi
#print axioms Sun28.Ordinary.pairHeight_phi_sharp
#print axioms Sun28.Ordinary.pairHeight_pos
#print axioms Sun28.Ordinary.logHeight_phi
#print axioms Sun28.Ordinary.radical_pos
#print axioms Sun28.Ordinary.radical_enlargement
#print axioms Sun28.Ordinary.finite_contact_height24
#print axioms Sun28.Ordinary.finite_contact_height_at_cutoff
#print axioms Sun28.Ordinary.glazer_five_height_transported
