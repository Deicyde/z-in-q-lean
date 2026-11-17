import ContactLocalSieve

namespace Sun28.WeightedSelection
open Sun28.ContactSieve Sun28.ContactFactors Sun28.NormSieve
noncomputable section

/-- A Gaussian choice above a prime tuple, including the prescribed congruences and bounds. -/
structure Candidate (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) where
  u : ℕ
  v : ℕ
  values : PrimeValues A u v
  gaussian : ↥(shifts A)→ManuscriptV15.Arithmetic.Gaussian
  positive : 0<v
  divisible : d∣v
  highSlope : H<(slope A u v:ℝ)
  highPrimes : ∀ r∈shifts A,Y<(values.value r:ℝ)
  rays : NormRays A values gaussian

def weight {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Candidate A d H Y) : ℝ :=
  ∏ r : ↥(shifts A),Real.log (a.values.value r.val)

theorem weight_pos {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Candidate A d H Y) : 0<weight a := by
  apply Finset.prod_pos
  intro r _
  exact Real.log_pos (by exact_mod_cast (a.values.prime r.val r.property).one_lt)

/-- The local clauses of the exact CRT test at a single specified prime. -/
def atPrime {ι : Type*} (π : ι→ManuscriptV15.Arithmetic.Gaussian) (T : Finset ℕ) (κ l : ℕ) : Prop :=
  (∀ r s,r≠s → ¬(forbidden l (π r) true ∧ forbidden l (π s) false)) ∧
  (l%4=1 → ∀ r,(ManuscriptV15.Arithmetic.gaussianNorm (π r):ZMod l)= -1 →
    ¬(realResidue l (π r)=0 ∧ imagResidue l (π r)^2= -1)) ∧
  (l∈T → ∀ r e,¬forbidden l (π r) e) ∧
  (l∈κ.primeFactors → l∉T → ∀ r,¬forbidden l (π r) false)

theorem residues_iff {ι : Type*} (π : ι→ManuscriptV15.Arithmetic.Gaussian)
    (T : Finset ℕ) (κ : ℕ) (primes : ∀ l∈T,l.Prime) :
    ResidueTests π T κ ↔ ∀ l : ℕ,l.Prime → l≠2 → l≠7 → atPrime π T κ l := by
  constructor
  · rintro ⟨mixed,diag,fix,aux⟩ l q odd seven
    exact ⟨fun r s ne => mixed r s ne l q odd seven,
      fun split r => diag r l q split,fun mem => fix l mem odd seven,
      fun mem out => aux l mem out odd seven⟩
  · intro h
    refine ⟨fun r s ne l q odd seven => (h l q odd seven).1 r s ne,?_,
      fun l mem odd seven => (h l (primes l mem) odd seven).2.2.1 mem,
      fun l mem out odd seven => (h l (Nat.prime_of_mem_primeFactors mem) odd seven).2.2.2 mem out⟩
    intro r l q split
    exact (h l q (by omega) (by omega)).2.1 split r

def below {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Candidate A d H Y) (T : Finset ℕ) (κ L : ℕ) : Prop :=
  ∀ l : ℕ,l.Prime → l≠2 → l≠7 → l≤L → atPrime a.gaussian T κ l

def tail {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (a : Candidate A d H Y) (T : Finset ℕ) (κ L : ℕ) : Prop :=
  ∃ l : ℕ,l.Prime ∧ l≠2 ∧ l≠7 ∧ L<l ∧ ¬atPrime a.gaussian T κ l

/-- At a fixed box the finite-cutoff mass exceeds the removed tail mass. -/
def surplus {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ L : ℕ)
    (S : Finset (Candidate A d H Y)) : Prop := by
  classical
  exact (∑ a∈S.filter (fun a => below a T κ L ∧ tail a T κ L),weight a) <
    ∑ a∈S.filter (fun a => below a T κ L),weight a

theorem survives {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} {T : Finset ℕ} {κ L : ℕ}
    {S : Finset (Candidate A d H Y)} (primes : ∀ l∈T,l.Prime) (win : surplus T κ L S) :
    ∃ a∈S,ResidueTests a.gaussian T κ := by
  classical
  by_contra! none
  have eq : S.filter (fun a => below a T κ L ∧ tail a T κ L)=S.filter (fun a => below a T κ L) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · rintro ⟨mem,b⟩
      refine ⟨mem,b,?_⟩
      by_contra nt
      apply none a mem
      apply (residues_iff a.gaussian T κ primes).mpr
      intro l q odd seven
      by_cases sm : l≤L
      · exact b l q odd seven sm
      · by_contra bad
        exact nt ⟨l,q,odd,seven,by omega,bad⟩
  unfold surplus at win
  rw [eq] at win
  exact (lt_irrefl _ win)

/-- The paper's remaining weighted prime-count application in the exact root family. -/
def PositiveSurplus : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ l∈T,l.Prime) → 2∈T →
      ∀ H Y : ℝ, ∃ (L : ℕ) (S : Finset (Candidate (Sun28.RealPoleBounds.fixedScale n) d H Y)),
        surplus T κ L S

theorem prime_values_iff_surplus : PrimeValuesWithResidues ↔ PositiveSurplus := by
  classical
  constructor
  · intro all X c q n roots d κ T dp kp primes two H Y
    obtain ⟨u,v,values,π,hv,div,hs,hy,rays,good⟩:=all X c q n roots d κ T dp kp primes two H Y
    let a : Candidate (Sun28.RealPoleBounds.fixedScale n) d H Y := ⟨u,v,values,π,hv,div,hs,hy,rays⟩
    have loc := (residues_iff π T κ primes).mp good
    have b : below a T κ 0 := fun l q odd seven _ => loc l q odd seven
    have nt : ¬tail a T κ 0 := fun ⟨l,q,odd,seven,_,bad⟩ => bad (loc l q odd seven)
    refine ⟨0,{a},?_⟩
    have low : ({a} : Finset _).filter (fun z => below z T κ 0)={a} := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · exact And.left
      · rintro rfl
        exact ⟨rfl,b⟩
    have none : ({a} : Finset _).filter (fun z => below z T κ 0 ∧ tail z T κ 0)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨mem,_,ht⟩:=Finset.mem_filter.mp hz
      obtain rfl:=Finset.mem_singleton.mp mem
      exact nt ht
    unfold surplus
    rw [low,none]
    simpa only [Finset.sum_empty,Finset.sum_singleton] using weight_pos a
  · intro all X c q n roots d κ T dp kp primes two H Y
    obtain ⟨L,S,win⟩:=all X c q n roots d κ T dp kp primes two H Y
    obtain ⟨a,_,ok⟩:=survives primes win
    exact ⟨a.u,a.v,a.values,a.gaussian,a.positive,a.divisible,a.highSlope,a.highPrimes,a.rays,ok⟩

end
end Sun28.WeightedSelection
#print axioms Sun28.WeightedSelection.weight_pos
#print axioms Sun28.WeightedSelection.residues_iff
#print axioms Sun28.WeightedSelection.survives
#print axioms Sun28.WeightedSelection.prime_values_iff_surplus
