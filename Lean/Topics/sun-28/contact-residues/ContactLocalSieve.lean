import SplitFibres

namespace Sun28.NormSieve
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.ContactSieve

def forbidden (l : ℕ) (z : Gaussian) (sign : Bool) : Prop :=
  if l%4=3 then
    realResidue l z=(if sign then -1 else 1) ∧ imagResidue l z=0
  else 2*realResidue l z = if sign then -((gaussianNorm z:ZMod l)+1) else (gaussianNorm z:ZMod l)+1

theorem forbidden_iff {l : ℕ} [Fact l.Prime] (odd : l≠2) (z : Gaussian) (sign : Bool) :
    forbidden l z sign ↔ l∣adjacentNorm z sign := by
  by_cases inert : l%4=3
  · simpa [forbidden,inert] using (inert_iff inert z sign).symm
  · have two : (2:ZMod l)≠0 := by
      rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
      exact fun d => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp d)
    rw [adjacent_iff odd]
    cases sign <;> simp [forbidden,inert,signedCoordinate,eq_div_iff two,mul_comm]

/-- Local residue exclusions for a whole tuple. The first two clauses treat
different shifts and the same shift separately. -/
def ResidueTests {ι : Type*} (π : ι→Gaussian) (T : Finset ℕ) (κ : ℕ) : Prop :=
  (∀ r s, r≠s → ∀ l : ℕ,l.Prime → l≠2 → l≠7 →
    ¬(forbidden l (π r) true ∧ forbidden l (π s) false)) ∧
  (∀ r, ∀ l : ℕ,l.Prime → l%4=1 → (gaussianNorm (π r):ZMod l) = -1 →
    ¬(realResidue l (π r)=0 ∧ (imagResidue l (π r))^2 = -1)) ∧
  (∀ l∈T,l≠2 → l≠7 → ∀ r e,¬forbidden l (π r) e) ∧
  (∀ l∈κ.primeFactors,l∉T → l≠2 → l≠7 → ∀ r,¬forbidden l (π r) false)

theorem local_iff {ι : Type*} (π : ι→Gaussian) (T : Finset ℕ) (κ : ℕ)
    (primes : ∀ l∈T,l.Prime) : MixedAndLocal π T κ ↔ ResidueTests π T κ := by
  constructor
  · rintro ⟨mix,fixed,aux⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro r s _ l prime odd seven tests
      let _ : Fact l.Prime:=⟨prime⟩
      exact mix r s l prime odd seven ⟨(forbidden_iff odd _ _).mp tests.1,(forbidden_iff odd _ _).mp tests.2⟩
    · intro r l prime spl _ z
      let _ : Fact l.Prime:=⟨prime⟩
      have odd : l≠2 := by omega
      exact mix r r l prime odd (by omega) ((diagonal_iff odd _).mpr z)
    · intro l mem odd seven r e h
      let _ : Fact l.Prime:=⟨primes l mem⟩
      exact fixed l mem odd seven r e ((forbidden_iff odd _ _).mp h)
    · intro l mem out odd seven r h
      let _ : Fact l.Prime:=⟨Nat.prime_of_mem_primeFactors mem⟩
      exact aux l mem out odd seven r ((forbidden_iff odd _ _).mp h)
  · rintro ⟨mix,self,fixed,aux⟩
    refine ⟨?_,?_,?_⟩
    · intro r s l prime odd seven d
      let _ : Fact l.Prime:=⟨prime⟩
      by_cases eq : r=s
      · subst s
        obtain ⟨spl,neg⟩:=self_obstruction odd (π r) d.1 d.2
        exact self r l prime spl neg ((diagonal_iff odd _).mp d)
      · exact mix r s eq l prime odd seven ⟨(forbidden_iff odd _ _).mpr d.1,(forbidden_iff odd _ _).mpr d.2⟩
    · intro l mem odd seven r e h
      let _ : Fact l.Prime:=⟨primes l mem⟩
      exact fixed l mem odd seven r e ((forbidden_iff odd _ _).mpr h)
    · intro l mem out odd seven r h
      let _ : Fact l.Prime:=⟨Nat.prime_of_mem_primeFactors mem⟩
      exact aux l mem out odd seven r ((forbidden_iff odd _ _).mpr h)

/-- The remaining simultaneous prime-value assertion with explicit residue tests. -/
def PrimeValuesWithResidues : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ), 0<d → 0<κ → (∀ l∈T,l.Prime) → 2∈T →
    ∀ H Y : ℝ, let A:=Sun28.RealPoleBounds.fixedScale n
      ∃ (u v : ℕ) (h : PrimeValues A u v) (π : ↥(shifts A)→Gaussian),
        0<v ∧ d∣v ∧ H<(slope A u v:ℝ) ∧ (∀ r∈shifts A,Y<(h.value r:ℝ)) ∧
        NormRays A h π ∧ ResidueTests π T κ

theorem pattern_iff : ContactSieve.PrimePatterns ↔ PrimeValuesWithResidues := by
  constructor <;> intro h X c q n roots d κ T dp kp primes two H Y
  · obtain ⟨u,v,values,π,hv,div,big,ahead,rays,mixed⟩:=h X c q n roots d κ T dp kp primes two H Y
    exact ⟨u,v,values,π,hv,div,big,ahead,rays,(local_iff π T κ primes).mp mixed⟩
  · obtain ⟨u,v,values,π,hv,div,big,ahead,rays,tests⟩:=h X c q n roots d κ T dp kp primes two H Y
    exact ⟨u,v,values,π,hv,div,big,ahead,rays,(local_iff π T κ primes).mpr tests⟩

end Sun28.NormSieve
#print axioms Sun28.NormSieve.forbidden_iff
#print axioms Sun28.NormSieve.local_iff
#print axioms Sun28.NormSieve.pattern_iff
