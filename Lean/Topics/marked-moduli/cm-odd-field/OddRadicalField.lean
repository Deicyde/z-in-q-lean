import TYZCompositum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-! Square classes in the actual multiquadratic field of an odd TYZ row. -/
namespace ZInQBlueprint.TYZ.Specialization
noncomputable section
open IntermediateField

private theorem belongs_iff_fixed (F : SubfieldQ) (a : K) :
    a ∈ F ↔ ∀ σ ∈ F.fixingSubgroup, σ a = a := by
  conv_lhs => rw [←InfiniteGalois.fixedField_fixingSubgroup F]
  exact IntermediateField.mem_fixedField_iff _ _

private theorem fixedBy_adjoin {z : K} {σ : Gal} (hs : σ z = z) :
    σ ∈ (IntermediateField.adjoin ℚ {z}).fixingSubgroup := by
  let U := Subgroup.zpowers σ
  have hle : IntermediateField.adjoin ℚ {z} ≤ IntermediateField.fixedField U := by
    apply IntermediateField.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    change z ∈ IntermediateField.fixedField U
    rw [IntermediateField.mem_fixedField_iff]
    intro τ h
    obtain ⟨k,rfl⟩ := h
    exact MulAction.mem_fixedBy_zpow (g := σ) (a := z) hs k
  apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
  intro a ha
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle ha) σ (Subgroup.mem_zpowers σ)

private theorem conjugate_sign (σ : Gal) {a : K} {q : ℚ} (ha : a^2 = (q:K)) :
    σ a = a ∨ σ a = -a := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [←map_pow,ha]
  exact σ.commutes q

/-- On adjoining a single square root, any element whose square is rational
either already belongs to the old field, or its product with that root does. -/
theorem squareRoot_quadratic_step {F : SubfieldQ} {z a : K} {d q : ℚ}
    (hz : z^2 = (d:K)) (ha : a^2 = (q:K))
    (hm : a ∈ F ⊔ IntermediateField.adjoin ℚ {z}) : a ∈ F ∨ a*z ∈ F := by
  classical
  by_cases inF : a ∈ F
  · exact Or.inl inF
  right
  obtain ⟨σ,hσ,hσa⟩ : ∃ σ ∈ F.fixingSubgroup, σ a ≠ a := by
    have h := mt (belongs_iff_fixed F a).mpr inF
    push Not at h
    exact h
  have neutral (τ : Gal) (hτ : τ ∈ F.fixingSubgroup) (hτz : τ z = z) : τ a = a := by
    apply (belongs_iff_fixed _ _).mp hm τ
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hτ,fixedBy_adjoin hτz⟩
  have hσz : σ z = -z := (conjugate_sign σ hz).resolve_left (fun h => hσa (neutral σ hσ h))
  have hneg : σ a = -a := (conjugate_sign σ ha).resolve_left hσa
  apply (belongs_iff_fixed F _).mpr
  intro τ hτ
  rw [map_mul]
  rcases conjugate_sign τ hz with hplus | hminus
  · rw [neutral τ hτ hplus,hplus]
  · have hprod : (σ*τ) z = z := by
      change σ (τ z) = z
      rw [hminus,map_neg,hσz,neg_neg]
    have hab : σ (τ a) = a := neutral (σ*τ) (F.fixingSubgroup.mul_mem hσ hτ) hprod
    have hτa : τ a = -a := by
      apply σ.injective
      rw [hab,map_neg,hneg,neg_neg]
    rw [hτa,hminus,neg_mul_neg]

/-- Rational square classes visible in the field all have even valuation at
two. This property places no restrictions on nonrational squares. -/
def EvenSquareClasses (F : SubfieldQ) : Prop :=
  ∀ (a : K) (q : ℚ), a ∈ F → a^2 = (q:K) → Even (padicValRat 2 q)

private theorem evenSquareClasses_bot : EvenSquareClasses ⊥ := by
  intro a q hm hq
  obtain ⟨z,rfl⟩ := IntermediateField.mem_bot.mp hm
  have eq : z^2 = q := by
    apply (algebraMap ℚ K).injective
    rw [map_pow]; exact hq
  rw [←eq,padicValRat.pow]
  exact ⟨padicValRat 2 z,by norm_num; ring⟩

/-- Adjoining a root of a nonzero rational of even valuation preserves the
parity restriction on every rational square class. -/
theorem evenSquareClasses_adjoin {F : SubfieldQ} (hF : EvenSquareClasses F)
    {z : K} {d : ℚ} (hd : d ≠ 0) (hv : Even (padicValRat 2 d)) (hz : z^2 = (d:K)) :
    EvenSquareClasses (F ⊔ IntermediateField.adjoin ℚ {z}) := by
  intro a q hm hq
  by_cases h0 : q = 0
  · simp [h0]
  rcases squareRoot_quadratic_step hz hq hm with ha | hp
  · exact hF a q ha hq
  · have prod : (a*z)^2 = ((q*d : ℚ):K) := by rw [mul_pow,hq,hz,Rat.cast_mul]
    have hval := hF _ _ hp prod
    rw [padicValRat.mul h0 hd] at hval
    obtain ⟨v,vh⟩ := hval
    obtain ⟨t,th⟩ := hv
    exact ⟨v-t,by omega⟩

theorem evenSquareClasses_radicalField {n : ℕ} (hn : Odd n) : EvenSquareClasses (radicalField n) := by
  classical
  have hi : EvenSquareClasses (IntermediateField.adjoin ℚ {Rank.sqrtMinus 1}) := by
    have sq : (Rank.sqrtMinus 1)^2 = (((-1):ℚ):K) := by simpa using Rank.sqrtMinus_sq 1
    simpa using evenSquareClasses_adjoin (F := ⊥) evenSquareClasses_bot (d := -1)
      (by norm_num) (by simp [padicValRat.neg]) sq
  have go (s : Finset ℕ) (hs : ∀ d ∈ s, Odd d) :
      EvenSquareClasses (IntermediateField.adjoin ℚ
        (insert (Rank.sqrtMinus 1) (sqrtDivisor '' (↑s : Set ℕ)))) := by
    induction s using Finset.induction_on with
    | empty => simpa using hi
    | @insert d s hd ih =>
      have hdodd := hs d (Finset.mem_insert_self ..)
      have hd0 : (d:ℚ) ≠ 0 := by
        have nz : d ≠ 0 := by obtain ⟨t,ht⟩ := hdodd; omega
        exact_mod_cast nz
      have hval : padicValRat 2 (d:ℚ) = 0 := by
        rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hdodd ∘ even_iff_two_dvd.mpr)]
        rfl
      have step := evenSquareClasses_adjoin (ih (fun e he => hs e (Finset.mem_insert_of_mem he)))
        (z := sqrtDivisor d) hd0 (by simp [hval])
        (by simpa using sqrtDivisor_sq d)
      convert step using 1
      rw [Finset.coe_insert,Set.image_insert_eq,Set.insert_comm (Rank.sqrtMinus 1),
        ←IntermediateField.adjoin_union,Set.union_singleton]
  apply go n.divisors
  intro d hd
  apply Nat.not_even_iff_odd.mp
  intro h
  exact (Nat.not_even_iff_odd.mpr hn) (h.trans_dvd (Nat.mem_divisors.mp hd).1)

/-- For every odd n the actual genus radical field Lₙ(i)=Q(i,√d : d∣n)
excludes √2, independently of the extended CM fields. -/
theorem sqrtTwo_not_mem_radicalField {n : ℕ} (hn : Odd n) : sqrtDivisor 2 ∉ radicalField n := by
  intro h
  have ev := evenSquareClasses_radicalField hn _ 2 h (by simpa using sqrtDivisor_sq 2)
  rw [show padicValRat 2 2 = 1 from padicValRat.self (by decide : 1 < 2)] at ev
  exact Int.not_even_one ev

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.squareRoot_quadratic_step
#print axioms ZInQBlueprint.TYZ.Specialization.evenSquareClasses_adjoin
#print axioms ZInQBlueprint.TYZ.Specialization.evenSquareClasses_radicalField
#print axioms ZInQBlueprint.TYZ.Specialization.sqrtTwo_not_mem_radicalField
