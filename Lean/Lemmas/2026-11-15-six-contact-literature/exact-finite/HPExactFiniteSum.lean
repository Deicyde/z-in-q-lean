import HPExceptionalOrders

/-! The finite part of the stable-discriminant formula is an elementary rational height. -/
namespace ZInQBlueprint.JacobianHeight.ExactFinite
open ZInQ SixContactHP
noncomputable section

private theorem pos_parts (j : ℚ) {p : ℕ} (hp : p.Prime) :
    max 0 (padicValRat p j)=(j.num.natAbs.factorization p:ℤ) ∧
    max 0 (-padicValRat p j)=(j.den.factorization p:ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := Rat.num_or_den_zero_padicVal j hp
  simp only [padicValRat_def,padicValInt,Nat.factorization_def _ hp] at h ⊢
  rcases h with h|h <;> omega

private theorem finiteTerm_factorization (K : Type) [Field K] [NumberField K] {u : ℚ}
    (hu : u ∉ contactSet) {p : ℕ} (hp : p.Prime) :
    finiteTerm K u p = (Module.finrank ℚ K : ℝ) *
      ((3*((SixContact.J u).num.natAbs.factorization p : ℝ)+2*((SixContact.J u).den.factorization p : ℝ)) *
        Real.log p) := by
  rw [finiteTerm_all_primes K hu hp,(pos_parts _ hp).1,(pos_parts _ hp).2]
  push_cast
  rfl

private theorem support_prime {u : ℚ} {p : ℕ} (h : p ∈ finiteSupport u) : p.Prime := by
  rcases Finset.mem_union.mp h with h|h
  · rcases Finset.mem_union.mp h with h|h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl|rfl <;> decide
    · exact Nat.prime_of_mem_primeFactors h
  · exact Nat.prime_of_mem_primeFactors h

private theorem zeros_subset {u : ℚ} (hu : u ∉ contactSet) :
    (SixContact.J u).num.natAbs.primeFactors ⊆ finiteSupport u := by
  intro p hp
  by_contra out
  have prime := Nat.prime_of_mem_primeFactors hp
  have h := finiteTerm_factorization ℚ hu prime
  rw [finiteTerm_off_support ℚ u out] at h
  have hmem : p ∈ (SixContact.J u).num.natAbs.factorization.support := by
    rwa [Nat.support_factorization]
  have e := Finsupp.mem_support_iff.mp hmem
  have positive : 0 < ((SixContact.J u).num.natAbs.factorization p : ℝ) :=
    by exact_mod_cast Nat.pos_of_ne_zero e
  have hd : 0 ≤ ((SixContact.J u).den.factorization p : ℝ) := by positivity
  have hl : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast prime.one_lt)
  rw [Module.finrank_self] at h
  have g : 0 < (3*((SixContact.J u).num.natAbs.factorization p : ℝ) +
        2*((SixContact.J u).den.factorization p : ℝ)) * Real.log p := by positivity
  simp only [Nat.cast_one,one_mul] at h
  exact g.ne' h.symm

private theorem sum_over_support {n : ℕ} {S : Finset ℕ} (hs : n.primeFactors ⊆ S) :
    ∑ p ∈ S, (n.factorization p:ℝ)*Real.log p = Real.log n := by
  rw [Real.log_nat_eq_sum_factorization]
  simp only [Finsupp.sum,Nat.support_factorization]
  symm
  apply Finset.sum_subset hs
  intro p _ out
  have hn : p ∉ n.factorization.support := by simpa only [Nat.support_factorization] using out
  simp [Finsupp.notMem_support_iff.mp hn]

/-- The full finite contribution on the rational paper family, with all local weights. -/
theorem finite_sum_eq (K : Type) [Field K] [NumberField K] {u : ℚ} (hu : u ∉ contactSet) :
    ∑ p ∈ finiteSupport u, finiteTerm K u p = (Module.finrank ℚ K : ℝ) *
      (3 * Real.log ((SixContact.J u).num.natAbs : ℝ) + 2 * Real.log ((SixContact.J u).den : ℝ)) := by
  let j := SixContact.J u
  let S := finiteSupport u
  calc
    _ = ∑ p ∈ S, (Module.finrank ℚ K:ℝ) *
        ((3*(j.num.natAbs.factorization p : ℝ)+2*(j.den.factorization p : ℝ))*Real.log p) :=
      Finset.sum_congr rfl (fun _ hp => finiteTerm_factorization K hu (support_prime hp))
    _ = (Module.finrank ℚ K:ℝ) *
        (3*(∑ p ∈ S, (j.num.natAbs.factorization p:ℝ)*Real.log p) +
         2*(∑ p ∈ S, (j.den.factorization p:ℝ)*Real.log p)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [sum_over_support (zeros_subset hu),sum_over_support (poles_subset u)]

/-- The HP formula on this family has no remaining finite-place or discriminant sum. -/
theorem paper_finite_formula (K : Type) [Field K] [NumberField K] {u : ℚ} (hu : u ∉ contactSet)
    (data : PaperFibreHeights K u) :
    (Module.finrank ℚ K : ℝ) * (data.stable + Real.log Real.pi) =
      (Module.finrank ℚ K : ℝ) *
        (3*Real.log ((SixContact.J u).num.natAbs : ℝ)+2*Real.log ((SixContact.J u).den : ℝ))/60 -
      (∑ σ, Real.log (peterssonFactor (data.period σ)))/10 := by
  rw [←finite_sum_eq K hu]
  exact data.heightFormula

end
end ZInQBlueprint.JacobianHeight.ExactFinite
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.finite_sum_eq
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.paper_finite_formula
