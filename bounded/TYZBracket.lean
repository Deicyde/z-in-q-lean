import TYZIntegerCoefficient

open Finset
open scoped BigOperators

namespace ZInQBlueprint.TYZ

/-- Integer factors in the second bracket on Tian--Yuan--Zhang p. 760.
We use these records only when d is five modulo eight. -/
@[ext] structure BracketTerm (d : ℕ) where
  d₀ : ℕ
  d₁ : ℕ
  rest : Finset ℕ
  d₀mod : d₀ % 8 = 7
  d₁mod : d₁ % 8 = 1 ∨ d₁ % 8 = 3
  d₁gt : 1 < d₁
  rest_factors : ∀ a ∈ rest, 1 < a ∧ a % 8 = 1
  product : d₀ * d₁ * (∏ a ∈ rest, a) = d

private theorem prod_one_mod_eight (R : Finset ℕ) (h : ∀ a ∈ R, a % 8 = 1) :
    (∏ a ∈ R, a) % 8 = 1 := by
  induction R using Finset.induction_on with
  | empty => decide
  | @insert a R ha ih =>
    rw [Finset.prod_insert ha, Nat.mul_mod, h a (mem_insert_self _ _),
      ih (fun b hb => h b (mem_insert_of_mem hb))]

/-- The alternative d₁ ≡ 1 printed on p. 760 cannot occur when d ≡ 5. -/
theorem BracketTerm.second_mod {d : ℕ} (hd : d % 8 = 5) (T : BracketTerm d) : T.d₁ % 8 = 3 := by
  rcases T.d₁mod with h | h
  · have hc := congrArg (fun x => x % 8) T.product
    change (T.d₀ * T.d₁ * (∏ a ∈ T.rest, a)) % 8 = d % 8 at hc
    rw [Nat.mul_mod, Nat.mul_mod T.d₀ T.d₁, T.d₀mod, h,
      prod_one_mod_eight T.rest (fun a ha => (T.rest_factors a ha).2), hd] at hc
    norm_num at hc
  · exact h

def BracketTerm.factors {d : ℕ} (T : BracketTerm d) : Finset ℕ :=
  insert T.d₀ (insert T.d₁ T.rest)

private theorem not_rest_of_mod {d a : ℕ} (T : BracketTerm d) (h : a % 8 ≠ 1) : a ∉ T.rest :=
  fun ha => h (T.rest_factors a ha).2

private theorem BracketTerm.distinct {d : ℕ} (hd : d % 8 = 5) (T : BracketTerm d) :
    T.d₀ ≠ T.d₁ ∧ T.d₀ ∉ T.rest ∧ T.d₁ ∉ T.rest := by
  have h0 := T.d₀mod
  have h1 := T.second_mod hd
  exact ⟨fun he => by rw [he] at h0; omega, not_rest_of_mod T (by omega),
    not_rest_of_mod T (by omega)⟩

private theorem BracketTerm.filter_eq {d : ℕ} (hd : d % 8 = 5) (T : BracketTerm d) :
    (T.factors.filter fun a => a % 8 = 7) = {T.d₀} ∧
    (T.factors.filter fun a => a % 8 = 3) = {T.d₁} := by
  have h0 := T.d₀mod
  have h1 := T.second_mod hd
  constructor
  · ext a
    simp only [BracketTerm.factors, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | ha), h⟩
      · rfl
      · omega
      · have := (T.rest_factors a ha).2
        omega
    · rintro rfl
      exact ⟨Or.inl rfl, h0⟩
  · ext a
    simp only [BracketTerm.factors, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | ha), h⟩
      · omega
      · rfl
      · have := (T.rest_factors a ha).2
        omega
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl), h1⟩

private theorem BracketTerm.valid {d : ℕ} (hd : d % 8 = 5) (T : BracketTerm d) :
    T.factors ∈ factorizations d ∧ Residues T.factors := by
  have h0 := T.d₀mod
  have h1 := T.second_mod hd
  obtain ⟨hne,h0R,h1R⟩ := T.distinct hd
  obtain ⟨hf7,hf3⟩ := T.filter_eq hd
  have h0I : T.d₀ ∉ insert T.d₁ T.rest := by simp [hne,h0R]
  constructor
  · apply (mem_factorizations (by omega) _).mpr
    constructor
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · omega
      rcases mem_insert.mp ha with rfl | ha
      · exact T.d₁gt
      · exact (T.rest_factors a ha).1
    · rw [BracketTerm.factors, prod_insert h0I, prod_insert h1R, ← Nat.mul_assoc]
      exact T.product
  · refine ⟨by rw [hf7]; simp, by rw [hf3]; simp, ?_⟩
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact Or.inl h0
    rcases mem_insert.mp ha with rfl | ha
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (T.rest_factors a ha).2)

private theorem unique_residue {F : Finset ℕ} {k : ℕ}
    (h : (F.filter fun a => a % 8 = k).card = 1) : ∃! a, a ∈ F ∧ a % 8 = k := by
  obtain ⟨a, heq⟩ := Finset.card_eq_one.mp h
  have ha : a ∈ F.filter (fun x => x % 8 = k) := by rw [heq]; simp
  refine ⟨a, mem_filter.mp ha, ?_⟩
  intro b hb
  have hmem : b ∈ F.filter (fun x => x % 8 = k) := mem_filter.mpr hb
  simpa only [heq, mem_singleton] using hmem

def admissibleFactorizations (d : ℕ) : Finset (Finset ℕ) := (factorizations d).filter Residues

theorem BracketTerm.factors_injective {d : ℕ} (hd : d % 8 = 5) :
    Function.Injective (@BracketTerm.factors d) := by
  intro S T heq
  have h0set := (S.filter_eq hd).1.symm.trans ((congrArg (Finset.filter (fun a : ℕ => a % 8 = 7)) heq).trans (T.filter_eq hd).1)
  have h1set := (S.filter_eq hd).2.symm.trans ((congrArg (Finset.filter (fun a : ℕ => a % 8 = 3)) heq).trans (T.filter_eq hd).2)
  have h0 : S.d₀ = T.d₀ := by simpa using h0set
  have h1 : S.d₁ = T.d₁ := by simpa using h1set
  have recover (U : BracketTerm d) : (U.factors.erase U.d₀).erase U.d₁ = U.rest := by
    obtain ⟨hne,h0R,h1R⟩ := U.distinct hd
    have hn : U.d₀ ∉ insert U.d₁ U.rest := by simp [hne,h0R]
    simp [BracketTerm.factors, hn, h1R]
  exact BracketTerm.ext h0 h1 (by rw [← recover S, heq, h0, h1, recover T])

theorem BracketTerm.exists_of_factors {d : ℕ} (hd : d % 8 = 5) {F : Finset ℕ}
    (hF : F ∈ admissibleFactorizations d) : ∃ T : BracketTerm d, T.factors = F := by
  obtain ⟨hfact, h7, h3, hall⟩ := mem_filter.mp hF
  obtain ⟨hlt,hprod⟩ := (mem_factorizations (by omega) F).mp hfact
  obtain ⟨a, ⟨ha, ha7⟩, hauniq⟩ := unique_residue h7
  obtain ⟨b, ⟨hb, hb3⟩, hbuniq⟩ := unique_residue h3
  have hab : a ≠ b := by intro he; rw [he] at ha7; omega
  have hbe : b ∈ F.erase a := mem_erase.mpr ⟨Ne.symm hab,hb⟩
  let R := (F.erase a).erase b
  have hR (r : ℕ) (hr : r ∈ R) : 1 < r ∧ r % 8 = 1 := by
    obtain ⟨hrb,hre⟩ := mem_erase.mp hr
    obtain ⟨hra,hrF⟩ := mem_erase.mp hre
    refine ⟨hlt r hrF, ?_⟩
    rcases hall r hrF with h | h | h
    · exact False.elim (hra (hauniq r ⟨hrF,h⟩))
    · exact False.elim (hrb (hbuniq r ⟨hrF,h⟩))
    · exact h
  have hmul : a * b * (∏ r ∈ R, r) = d := by
    rw [Nat.mul_assoc]
    change a * (b * (∏ r ∈ (F.erase a).erase b, r)) = d
    rw [(F.erase a).mul_prod_erase (fun r => r) hbe, F.mul_prod_erase (fun r => r) ha, hprod]
  refine ⟨⟨a, b, R, ha7, Or.inr hb3, hlt b hb, hR, hmul⟩, ?_⟩
  change insert a (insert b ((F.erase a).erase b)) = F
  rw [insert_erase hbe, insert_erase ha]

/-- No order or multiplicity of the residual factors is introduced by marking the
two factors of different residues. In particular, R may be empty. -/
noncomputable def bracketEquiv (d : ℕ) (hd : d % 8 = 5) :
    BracketTerm d ≃ ↥(admissibleFactorizations d) :=
  Equiv.ofBijective (fun T => ⟨T.factors, mem_filter.mpr (T.valid hd)⟩)
    ⟨fun _ _ h => BracketTerm.factors_injective hd (congrArg Subtype.val h),
     fun F => by
       obtain ⟨T, hT⟩ := BracketTerm.exists_of_factors hd F.property
       exact ⟨T, Subtype.ext hT⟩⟩

theorem empty_rest (a b : ℕ) (ha : a % 8 = 7) (hb : b % 8 = 3) :
    ∃ T : BracketTerm (a*b), T.d₀ = a ∧ T.d₁ = b ∧ T.rest = ∅ := by
  refine ⟨⟨a,b,∅,ha,Or.inr hb,by omega,by simp,by simp⟩,rfl,rfl,rfl⟩


/-- The marked product has exactly the two distinguished class-group factors. -/
theorem BracketTerm.weight {M : Type*} [CommMonoid M] {d : ℕ} (hd : d % 8 = 5)
    (T : BracketTerm d) (w : ℕ → M) :
    (∏ a ∈ T.factors, w a) = w T.d₀ * w T.d₁ * ∏ r ∈ T.rest, w r := by
  obtain ⟨hne,h0R,h1R⟩ := T.distinct hd
  have hn : T.d₀ ∉ insert T.d₁ T.rest := by simp [hne,h0R]
  rw [BracketTerm.factors, Finset.prod_insert hn, Finset.prod_insert h1R, mul_assoc]

/-- The second integer coefficient on p. 760, expressed with its two
distinguished factors and a product over an unordered residual set. -/
noncomputable def printedCoefficient (d : ℕ) (hd : d % 8 = 5) : ℕ :=
  letI : Fintype (BracketTerm d) := Fintype.ofEquiv _ (bracketEquiv d hd).symm
  ∑ T : BracketTerm d, genusNumber T.d₀ * genusNumber T.d₁ * ∏ r ∈ T.rest, genusNumber r

theorem printedCoefficient_eq_integerCoefficient {d : ℕ} (hd : d % 8 = 5) :
    printedCoefficient d hd = integerCoefficient d := by
  classical
  let e := bracketEquiv d hd
  let _ : Fintype (BracketTerm d) := Fintype.ofEquiv _ e.symm
  change (∑ T : BracketTerm d, genusNumber T.d₀ * genusNumber T.d₁ * ∏ r ∈ T.rest, genusNumber r) = _
  calc
    _ = ∑ T : BracketTerm d, ∏ a ∈ (e T).val, genusNumber a := by
      exact Finset.sum_congr rfl fun T _ => (T.weight hd genusNumber).symm
    _ = ∑ F : ↥(admissibleFactorizations d), ∏ a ∈ F.val, genusNumber a :=
      e.sum_comp (fun F => ∏ a ∈ F.val, genusNumber a)
    _ = ∑ F ∈ admissibleFactorizations d, ∏ a ∈ F, genusNumber a :=
      Finset.sum_coe_sort (admissibleFactorizations d) (fun F => ∏ a ∈ F, genusNumber a)
    _ = _ := by rw [admissibleFactorizations, Finset.sum_filter]; rfl

theorem printedCoefficient_mod_two {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d) :
    (printedCoefficient d hd : ZMod 2) = ZInQ.RouteK.Rank5b.T5bCl d := by
  rw [printedCoefficient_eq_integerCoefficient hd, integerCoefficient_mod_two hs]


/-- Prime-block partitions admitted by the public predicate, in bijection with
the integer tuples in the second bracket of the published formula. -/
noncomputable def admissiblePartitionEquiv {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d) :
    {P : PrimePartition d // ZInQ.RouteK.Rank5b.Admissible5bNat d P} ≃ BracketTerm d := by
  let e : {P : PrimePartition d // ZInQ.RouteK.Rank5b.Admissible5bNat d P} ≃
      ↥(admissibleFactorizations d) := {
    toFun := fun P => ⟨factors P.val,
      mem_filter.mpr ⟨factors_mem hs P.val, (residues_factors P.val).mpr P.property⟩⟩
    invFun := fun F => by
      obtain ⟨hF, hR⟩ := mem_filter.mp F.property
      refine ⟨partitionOf hs F.val hF, (residues_factors _).mp ?_⟩
      rwa [factors_partitionOf]
    left_inv := fun P => Subtype.ext (factors_injective (factors_partitionOf hs (factors_mem hs P.val)))
    right_inv := fun F => Subtype.ext (factors_partitionOf hs (mem_filter.mp F.property).1)
  }
  exact e.trans (bracketEquiv d hd).symm

#print axioms admissiblePartitionEquiv

#print axioms printedCoefficient_eq_integerCoefficient
#print axioms printedCoefficient_mod_two

#print axioms BracketTerm.second_mod
#print axioms bracketEquiv
#print axioms empty_rest

end ZInQBlueprint.TYZ
