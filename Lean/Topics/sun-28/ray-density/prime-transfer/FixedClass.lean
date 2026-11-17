import IdealRows

namespace Sun28.PrimeTransfer
open Finset Sun28.RayDensity Sun28.RayDensity.Artin Sun28.Reciprocity Sun28.FinitePattern
open scoped Classical
noncomputable section

/-- The residue is 1+3i at 7 and i at every other odd factor. -/
def fixedOdd {K : ℕ} (v : Slot K) : GU v.val :=
  if h : v.val=7 then
    unitOf (p:=v.val) 1 3 (by
      have nd : ¬ v.val ∣ 10 := by rw [h]; decide
      have nz := (ZMod.natCast_eq_zero_iff 10 v.val).not.mpr nd
      norm_num at nz ⊢
      exact nz)
  else unitOf (p:=v.val) 0 1 (by norm_num)

def fixedWord (K : ℕ) : RayUnits (moduli K) :=
  (⟨(9,0), by decide⟩, fixedOdd)

theorem fixed_admissible (K : ℕ) : admissible K (fixedWord K) := by
  refine ⟨rfl,?_,?_⟩
  · show coords (fixedOdd (seven K)) = (1,3)
    simp [fixedOdd,seven,coords]
  · intro i away e
    have hp : 2 < i.val := by have := i.2.1.two_le; omega
    have nz : (2:ZMod i.val)≠0 := by
      simpa only [Nat.cast_ofNat] using ((ZMod.natCast_eq_zero_iff 2 i.val).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp))
    cases e <;> simpa [fixedWord,fixedOdd,away,adjacent,coords,one_add_one_eq_two] using nz

/-- A set of ordinary rational primes selected by a single fixed ideal-ray class. -/
def oneClass (K : ℕ) (p : ℕ) : Prop := p.Prime ∧
  ∃ J : coprimeIdeals (M (moduli K)), Nat.card (GaussianInt ⧸ J.val)=p ∧
    idealCoordinates (moduli K) (level_coprime K) (J:idealRay (moduli K))=fixedWord K

theorem fixed_class_common (K p : ℕ) (h : oneClass K p) : commonPrime K K p := by
  obtain ⟨prime,J,N,word⟩ := h
  exact selected_to_integer prime ⟨J,N,word ▸ fixed_admissible K⟩

/-- Directly testable interior prime weights, dominated by the exact base sample. -/
def classWeight (K : ℕ) (u : ℕ) : ℝ :=
  if oneClass K u then Real.log u else 0

theorem class_weight_le (K u : ℕ) : 0 ≤ classWeight K u ∧ classWeight K u ≤ primeWeight K K (u:ℤ) := by
  by_cases alive : oneClass K u
  · have good := fixed_class_common K u alive
    simp [classWeight,alive,primeWeight,good,Real.log_nonneg (by exact_mod_cast good.1.one_le : 1≤(u:ℝ))]
  · have pos : 0 ≤ primeWeight K K (u:ℤ) := by
      unfold primeWeight
      split
      next h => exact Real.log_nonneg (by exact_mod_cast h.2.1.one_le)
      next => rfl
    simp [classWeight,alive,pos]

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.fixed_admissible
#print axioms Sun28.PrimeTransfer.fixed_class_common
#print axioms Sun28.PrimeTransfer.class_weight_le
