import OrdinaryProducts

/-! The five original projective contact divisors pull back to Sun's marked forms
under an integral unimodular coordinate change. -/
namespace Sun28.Ordinary
open BigOperators

/-- In the order infinity, zero, one, 2401, -343/32. -/
def oldForm (i : Fin 5) (A B : ℤ) : ℤ :=
  ![B,A,A-B,A-2401*B,32*A+343*B] i

def transportedMark (i : Fin 5) : ℚ := ![0,-1/2,-1,1/2399,-32/407] i

def pulledForm (i : Fin 5) (U V : ℤ) : ℤ :=
  ![U,2*U+V,U+V,2399*U-V,407*U+32*V] i

theorem old_form_pullback (i : Fin 5) (U V : ℤ) :
    oldForm i (2*U+V) U = (if i=3 then -1 else 1)*pulledForm i U V := by
  fin_cases i <;> norm_num [oldForm,pulledForm] <;> ring

theorem reduced_forms (i : Fin 5) (t : ℚ) :
    pulledForm i t.num t.den=contactForm t (transportedMark i) := by
  fin_cases i <;> norm_num [pulledForm,transportedMark,contactForm] <;> ring

theorem marks_image (q : ℚ) : q∈marks ↔ ∃ i : Fin 5, transportedMark i=q := by
  simp only [marks,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (rfl|rfl|rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [transportedMark]

/-- A representative is primitive exactly when its image under phi is primitive. -/
theorem primitive_phi (U V : ℤ) : Int.gcd (2*U+V) U = Int.gcd U V := by
  apply Nat.dvd_antisymm
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd
    · exact Int.gcd_dvd_right _ _
    · have a := Int.gcd_dvd_left (2*U+V) U
      have b := Int.gcd_dvd_right (2*U+V) U
      have c := dvd_sub a (dvd_mul_of_dvd_right b 2)
      simpa using c
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd
    · exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left U V) 2) (Int.gcd_dvd_right U V)
    · exact Int.gcd_dvd_left U V

/-- For arbitrary homogeneous representatives this is equality of the exact
p-adic minima, expressed by the additive order of the common gcd.
For primitive representatives both are zero, including at 2. -/
theorem normalization_phi (p : ℕ) (U V : ℤ) :
    padicValNat p (Int.gcd (2*U+V) U)=padicValNat p (Int.gcd U V) := by rw [primitive_phi]

/-- Old projective contact primes, computed on a primitive coordinate pair. -/
def oldContactPrimes (S : Finset ℕ) (A B : ℤ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin 5)).biUnion fun i =>
    (oldForm i A B).natAbs.primeFactors.filter fun p => Odd (padicValInt p (oldForm i A B))) \ S

theorem mem_oldContactPrimes {p : ℕ} {S : Finset ℕ} {A B : ℤ} :
    p∈oldContactPrimes S A B ↔ p.Prime ∧ p∉S ∧ ∃ i : Fin 5,
      0<padicValInt p (oldForm i A B) ∧ Odd (padicValInt p (oldForm i A B)) := by
  classical
  simp only [oldContactPrimes,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨i,⟨prime,_,_⟩,odd⟩,outside⟩
    exact ⟨prime,outside,i,by obtain ⟨k,hk⟩ := odd; omega,odd⟩
  · rintro ⟨prime,outside,i,pos,odd⟩
    have nz : (oldForm i A B).natAbs≠0 := by intro e; simp [padicValInt,e] at pos
    exact ⟨⟨i,⟨prime,dvd_of_one_le_padicValNat pos,nz⟩,odd⟩,outside⟩

theorem old_depth_eq_projective (p : ℕ) (i : Fin 5) (t : ℚ) :
    padicValInt p (oldForm i (2*t.num+t.den) t.num)=padicValInt p (contactForm t (transportedMark i)) := by
  rw [old_form_pullback,reduced_forms]
  split_ifs <;> simp [padicValInt]

/-- Literal equality of the two finite sets in the completed detector for every S.
No primes are lost in the projective coordinate change. -/
theorem transported_contact_primes (S : Finset ℕ) (t : ℚ) :
    oldContactPrimes S (2*t.num+t.den) t.num=contactPrimes S t := by
  ext p
  rw [mem_oldContactPrimes,mem_contactPrimes]
  simp only [old_depth_eq_projective]
  constructor
  · rintro ⟨prime,outside,i,pos,odd⟩
    exact ⟨prime,outside,transportedMark i,(marks_image _).mpr ⟨i,rfl⟩,pos,odd⟩
  · rintro ⟨prime,outside,q,mark,pos,odd⟩
    obtain ⟨i,rfl⟩ := (marks_image q).mp mark
    exact ⟨prime,outside,i,pos,odd⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.old_form_pullback
#print axioms Sun28.Ordinary.reduced_forms
#print axioms Sun28.Ordinary.marks_image
#print axioms Sun28.Ordinary.primitive_phi
#print axioms Sun28.Ordinary.normalization_phi
#print axioms Sun28.Ordinary.mem_oldContactPrimes
#print axioms Sun28.Ordinary.old_depth_eq_projective
#print axioms Sun28.Ordinary.transported_contact_primes
