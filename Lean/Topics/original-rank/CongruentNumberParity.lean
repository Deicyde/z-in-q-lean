import ZInQKernel.Contrib.TYZDecomp.Leaves
import TYZIntegerCoefficient

open Finset
open scoped BigOperators
open ZInQ.RouteK.Rank5b ZInQ.PropN ZInQ.Contrib.TYZDecomp

namespace ZInQBlueprint.OriginalRank

/-- For a squarefree integer that is 1 or 3 modulo 8, all factors are
1 modulo 8 except, possibly, one factor that is 3 modulo 8. -/
def AdmissibleFactors (F : Finset ℕ) : Prop :=
  (∀ a ∈ F, a % 8 = 1 ∨ a % 8 = 3) ∧ (F.filter (fun a => a % 8 = 3)).card ≤ 1

instance (F : Finset ℕ) : Decidable (AdmissibleFactors F) := by
  unfold AdmissibleFactors
  infer_instance

/-- The right side of Tian–Yuan–Zhang, Theorem 1.1, for the odd residue
classes. At one the empty factorization contributes the empty product. -/
noncomputable def genusCoefficient (m : ℕ) : ℕ :=
  ∑ F ∈ TYZ.factorizations m, if AdmissibleFactors F then ∏ a ∈ F, TYZ.genusNumber a else 0

theorem genusCoefficient_mod_two {m : ℕ} (hs : Squarefree m) :
    (genusCoefficient m : ZMod 2) = Lam m := by
  classical
  let e : TYZ.PrimePartition m ↪ Finset ℕ := ⟨TYZ.factors, TYZ.factors_injective⟩
  have hf : TYZ.factorizations m = (univ : Finset (TYZ.PrimePartition m)).map e := by
    ext F
    rw [mem_map]
    constructor
    · intro hF
      exact ⟨TYZ.partitionOf hs F hF, mem_univ _, TYZ.factors_partitionOf hs hF⟩
    · rintro ⟨P, _, rfl⟩
      exact TYZ.factors_mem hs P
  rw [genusCoefficient, Nat.cast_sum, hf, Finset.sum_map, Lam]
  apply Finset.sum_congr rfl
  intro P _
  change ((if AdmissibleFactors (TYZ.factors P) then ∏ a ∈ TYZ.factors P, TYZ.genusNumber a else 0 : ℕ) : ZMod 2) = _
  have ha : AdmissibleFactors (TYZ.factors P) ↔ LamAdm m P := by
    unfold AdmissibleFactors LamAdm TYZ.factors
    simp only [filter_map, card_map, forall_mem_map]
    rfl
  by_cases h : LamAdm m P
  · rw [ite_eq_left (ha.mpr h), ite_eq_left h, Nat.cast_prod, TYZ.factors, Finset.prod_map]
    change (∏ B ∈ P.parts, (TYZ.genusNumber (dProd B) : ZMod 2)) = _
    simp only [TYZ.genusNumber_dProd]
  · rw [ite_eq_right (fun hh => h (ha.mp hh)), ite_eq_right h, Nat.cast_zero]

theorem genusCoefficient_one : genusCoefficient 1 = 1 := by
  classical
  rw [genusCoefficient]
  have h : TYZ.factorizations 1 = {∅} := by
    ext F
    rw [TYZ.mem_factorizations one_ne_zero F, Finset.mem_singleton]
    constructor
    · intro hF
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hd : a ∣ 1 := by
        rw [← hF.2]
        exact Finset.dvd_prod_of_mem id ha
      have := hF.1 a ha
      simp_all
    · rintro rfl
      simp
  simp [h, AdmissibleFactors]

/-- The odd part of Theorem 1.1 (Asian J. Math. 21, p. 723).
Each coefficient is required to have one integer square root with the
printed parity. No simultaneous choices of signs appear in this statement. -/
def OddCentralValueParity : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) →
    ∃ a : ℤ, (a : ℂ) ^ 2 = lcalSq m ∧ (a : ZMod 2) = (genusCoefficient m : ZMod 2)

theorem same_parity_of_complex_squares {a b : ℤ} (h : (a : ℂ) ^ 2 = (b : ℂ) ^ 2) :
    (a : ZMod 2) = (b : ZMod 2) := by
  have hint : a ^ 2 = b ^ 2 := by exact_mod_cast h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hint with hab | hab
  · rw [hab]
  · rw [hab, Int.cast_neg]
    have hone : -(1 : ZMod 2) = 1 := by decide
    simpa only [neg_mul, one_mul] using congrArg (fun x : ZMod 2 => x * (b : ZMod 2)) hone

theorem oddCentralValueParity_iff :
    OddCentralValueParity ↔ TYZThm11Integral ∧ TYZThm11Mod2 := by
  constructor
  · intro h
    constructor
    · intro m hs hm
      obtain ⟨a, ha, _⟩ := h m hs hm
      exact ⟨a, ha⟩
    · intro f hf m hs hm
      obtain ⟨a, ha, hp⟩ := h m hs hm
      exact (same_parity_of_complex_squares ((hf m hs hm).trans ha.symm)).trans
        (hp.trans (genusCoefficient_mod_two hs))
  · rintro ⟨hi, hp⟩
    classical
    let f (m : ℕ) : ℤ := if h : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) then
      (hi m h.1 h.2).choose else 0
    have hf (m : ℕ) (hs : Squarefree m) (hm : m % 8 = 1 ∨ m % 8 = 3) :
        (f m : ℂ) ^ 2 = lcalSq m := by
      simpa [f, hs, hm] using (hi m hs hm).choose_spec
    intro m hs hm
    exact ⟨f m, hf m hs hm, (hp f hf m hs hm).trans (genusCoefficient_mod_two hs).symm⟩

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.genusCoefficient_mod_two
#print axioms ZInQBlueprint.OriginalRank.genusCoefficient_one
#print axioms ZInQBlueprint.OriginalRank.same_parity_of_complex_squares
#print axioms ZInQBlueprint.OriginalRank.oddCentralValueParity_iff
