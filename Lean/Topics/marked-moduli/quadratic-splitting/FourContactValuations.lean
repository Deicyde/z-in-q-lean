import ThreeQuadraticFields

/-! The square classes of quartic products of rational differences and their allowed primes. -/
namespace ZInQBlueprint.BranchHeight
noncomputable section
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

private theorem mark_integral {p : ℕ} {c : ℚ} (hc : c ∈ ZInQ.contactSet) :
    0 ≤ padicValRat p c := by
  have hd : c.den = 1 := by
    simp [ZInQ.contactSet] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [padicValRat_def,hd]
  simp

private theorem val_prod {ι : Type*} (s : Finset ι) (g : ι → ℚ) (hg : ∀ i ∈ s, g i ≠ 0) :
    padicValRat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValRat p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,padicValRat.mul (hg a (Finset.mem_insert_self ..))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi))]
    rw [ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- Outside the odd-contact support the valuations of any four marked differences
sum to an even number. The four marks need not be pairwise distinct. -/
theorem even_four_contact_product {S : Finset ℕ} {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hS : p ∉ S) (hout : ¬p ∣ ZInQ.contactSupport S u)
    (c : Fin 4 → ℚ) (hc : ∀ i, c i ∈ ZInQ.contactSet) :
    Even (padicValRat p (∏ i, (u-c i))) := by
  have hn (i : Fin 4) : u-c i ≠ 0 := sub_ne_zero.mpr (fun h => hu (h ▸ hc i))
  rw [val_prod Finset.univ (fun i => u-c i) (fun i _ => hn i)]
  by_cases h : 0 ≤ padicValRat p u
  · have he (i : Fin 4) : Even (padicValRat p (u-c i)) := by
      have hneg : 0 ≤ padicValRat p (-c i) := by rw [padicValRat.neg]; exact mark_integral (hc i)
      have hdiff : 0 ≤ padicValRat p (u-c i) := by
        rw [sub_eq_add_neg]
        exact (le_min h hneg).trans (padicValRat.min_le_padicValRat_add (by simpa [sub_eq_add_neg] using hn i))
      rcases (Int.even_or_odd (padicValRat p (u-c i))) with h' | h'
      · exact h'
      · have hpos : 0 < padicValRat p (u-c i) := by obtain ⟨k,hk⟩ := h'; omega
        exact (hout ((ZInQ.prime_dvd_contactSupport_iff hu (Fact.out : Nat.Prime p)).mpr
          ⟨hS,c i,hc i,hpos,h'⟩)).elim
    simpa [Fin.sum_univ_succ] using ((he 0).add ((he 1).add ((he 2).add (he 3))))
  · have hu0 : u ≠ 0 := fun h => hu (by simp [h,ZInQ.contactSet])
    have he (i : Fin 4) : padicValRat p (u-c i) = padicValRat p u := by
      by_cases hz : c i = 0
      · simp [hz]
      · rw [sub_eq_add_neg]
        apply padicValRat.add_eq_of_lt (by simpa [sub_eq_add_neg] using hn i) hu0 (neg_ne_zero.mpr hz)
        rw [padicValRat.neg]
        exact lt_of_lt_of_le (lt_of_not_ge h) (mark_integral (hc i))
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact ⟨2*padicValRat p u,by ring⟩

/-- Multiplying the radicand by a rational p-adic unit preserves the parity. -/
theorem even_scaled_four_contact_product {S : Finset ℕ} {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hS : p ∉ S) (hout : ¬p ∣ ZInQ.contactSupport S u)
    (c : Fin 4 → ℚ) (hc : ∀ i, c i ∈ ZInQ.contactSet)
    {a : ℚ} (ha : a ≠ 0) (hv : padicValRat p a = 0) :
    Even (padicValRat p (a * ∏ i, (u-c i))) := by
  have hn : ∏ i, (u-c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => sub_ne_zero.mpr (fun h => hu (h ▸ hc i)))
  rw [padicValRat.mul ha hn,hv,zero_add]
  exact even_four_contact_product hu hS hout c hc

/-- The constants in the three quadratic discriminant classes are p-adic units
at every prime larger than five. -/
theorem radicand_scalar_units (hp : 5 < p) :
    padicValRat p 6 = 0 ∧ padicValRat p 10 = 0 ∧ padicValRat p (-15) = 0 := by
  have unit (v : ℕ) (hv : v ∣ Nat.factorial 5) : padicValRat p (v : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (fun h =>
      (Nat.not_le_of_gt hp) ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp (h.trans hv)))]
    rfl
  refine ⟨unit 6 ⟨20,by norm_num [Nat.factorial]⟩, unit 10 ⟨12,by norm_num [Nat.factorial]⟩, ?_⟩
  rw [padicValRat.neg]
  exact unit 15 ⟨8,by norm_num [Nat.factorial]⟩

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.even_four_contact_product
#print axioms ZInQBlueprint.BranchHeight.even_scaled_four_contact_product
#print axioms ZInQBlueprint.BranchHeight.radicand_scalar_units
