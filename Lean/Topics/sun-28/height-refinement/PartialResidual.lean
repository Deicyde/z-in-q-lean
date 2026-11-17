import PartialSector

namespace Sun28.HeightRefinement
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget
  Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors
  ZInQ.RouteK
noncomputable section
set_option exponentiation.threshold 160
set_option maxRecDepth 8192

/-- Holding the inverted primes fixed, absorb every even power available
in the selected square. The height cost of the cofactor can only decrease. -/
theorem absorb_square {A B b w c : ℤ} {i : Fin 5} (off : oldForm i A B≠0)
    (initial:Admissible i A B b (w^2*c)) (same:primeBase (b*w)=primeBase b) :
    Admissible i A B (b*w) c := by
  obtain ⟨split,small,mixed⟩:=initial
  have cn:c≠0:=fun z=>off (by simp [split,z])
  have wn:w≠0:=fun z=>off (by simp [split,z])
  have z: numberLog c≤numberLog (w^2*c):=by
    rw [log_mul_int (pow_ne_zero _ wn) cn]
    exact le_add_of_nonneg_left (nonneg_numberLog (pow_ne_zero _ wn))
  refine ⟨by rw [split];ring,same ▸ small,?_⟩
  rw [same]
  exact (mul_le_mul_of_nonneg_left z (mul_nonneg (by positivity) (by positivity))).trans mixed

theorem one_square {A B : ℤ} (i : Fin 5)
    (test:(ell (heightRadical A B))^4*numberLog (oldForm i A B)≤625*(heightRadical A B:ℝ)^23) :
    Admissible i A B 1 (oldForm i A B) := by
  have p:primeBase 1=1:=by norm_num [primeBase,primeProduct]
  have t:1≤heightRadical A B:=Nat.mul_pos pos_cutoff (pos_odd A B)
  simpa only [Admissible,one_pow,one_mul,p,Nat.cast_one,true_and] using And.intro t test

/-- Normalizing the full square part recovers the unrestricted denominator
radical test. This direction also identifies the signed squarefree cofactor. -/
theorem full_square {A B : ℤ} (off:∀ i,oldForm i A B≠0) (i : Fin 5)
    (old:primeProduct (repeatedPrimes i A B)≤heightRadical A B) :
    ∃ b : ℤ,Admissible i A B b (kernel i A B) := by
  obtain ⟨_,b,bn,fe⟩:=sqfInt_spec (off i)
  change oldForm i A B=kernel i A B*b^2 at fe
  have kn:kernel i A B≠0:=(sqfInt_spec (off i)).1.ne_zero
  have sub : b.natAbs.primeFactors⊆repeatedPrimes i A B := by
    intro p hp
    have prime:=Nat.prime_of_mem_primeFactors hp
    have sq:p^2∣(oldForm i A B).natAbs:=by
      rw [fe,Int.natAbs_mul,Int.natAbs_pow]
      exact (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) _).trans (dvd_mul_left _ _)
    have div:p∣(oldForm i A B).natAbs:=(dvd_pow_self _ two_ne_zero).trans sq
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨prime,div,Int.natAbs_ne_zero.mpr (off i)⟩,sq⟩
  have dt:primeBase b≤heightRadical A B :=
    (support_mono sub (fun _ h=>Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1)).trans old
  let T:ℝ:=heightRadical A B
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0<T:=by linarith
  have d:(primeBase b:ℝ)≤T:=by dsimp only [T];exact_mod_cast dt
  have z:numberLog (kernel i A B)≤T:=calc
    _≤Real.log T:= Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr kn) (Nat.cast_le.mpr (kernel_bound off i))
    _≤ T:=(Real.log_le_sub_one_of_pos tp).trans (by linarith)
  refine ⟨b,by simpa only [mul_comm] using fe,dt,?_⟩
  change _≤625*T^23
  calc
    _≤(T^20*(625*T))*T:=mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) d _)
      (ell_four t) (by positivity) (by positivity)) z (nonneg_numberLog kn) (by positivity)
    _=625*T^22:=by ring
    _≤_:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t (by decide)) (by norm_num)

/-- One test per divisor of a square, the existing four-place test, and the
minimum of ten unit-conductor bounds give the whole remaining problem. -/
def MixedResidual : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬Admissible i A B b c) → target A B

theorem original_iff_mixed (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ MixedResidual := by
  classical
  constructor
  · exact fun full A B cop off _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_partial units pell classes formula).mpr
    exact fun A B cop off _ sparse _ high no=>rem A B cop off sparse high no

theorem mixed_iff_previous : MixedResidual ↔ Residual := by
  constructor
  · exact fun h A B cop off _ sparse _ hi no=>h A B cop off sparse hi no
  · intro h A B cop off sparse hi no
    apply h A B cop off ?_ sparse ?_ hi no
    · intro i;exact lt_of_not_ge (fun old=>no i 1 _ (one_square i old))
    · intro i;apply lt_of_not_ge;intro old
      obtain ⟨b,test⟩:=full_square off i old
      exact no i b _ test

end
end Sun28.HeightRefinement
#print axioms Sun28.HeightRefinement.absorb_square
#print axioms Sun28.HeightRefinement.one_square
#print axioms Sun28.HeightRefinement.full_square
#print axioms Sun28.HeightRefinement.original_iff_mixed
#print axioms Sun28.HeightRefinement.mixed_iff_previous
