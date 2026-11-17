import ThomaeEighthPowers
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Algebraic branch points in the odd model of a smooth rational sextic. -/
namespace ZInQBlueprint.ThetaPeriod
open ThetaQuotient SexticThetaHeight Polynomial
noncomputable section

abbrev Partition := {S : Finset (Fin 5) // S.card = 2}

def differences (r : Fin 5 → ℂ) (S : Finset (Fin 5)) : ℂ :=
  ∏ i ∈ S, ∏ j ∈ S.filter (i < ·), (r i - r j)

def branchValue (r : Fin 5 → ℂ) (S : Partition) : ℂ :=
  (differences r S.val * differences r (Finset.univ \ S.val))^2

theorem differences_nonzero (r : Fin 5 → ℂ) (hr : Function.Injective r) (S : Finset (Fin 5)) :
    differences r S ≠ 0 := by
  unfold differences
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr fun he => (Finset.mem_filter.mp hj).2.ne (hr he)

theorem differences_algebraic (r : Fin 5 → ℂ) (hr : ∀ i, IsAlgebraic ℚ (r i))
    (S : Finset (Fin 5)) : IsAlgebraic ℚ (differences r S) := by
  exact (IsIntegral.prod _ fun i _ =>
    IsIntegral.prod _ fun j _ => (hr i).isIntegral.sub (hr j).isIntegral).isAlgebraic

theorem branchValue_nonzero (r : Fin 5 → ℂ) (hr : Function.Injective r) (S : Partition) :
    branchValue r S ≠ 0 :=
  pow_ne_zero _ (mul_ne_zero (differences_nonzero _ hr _) (differences_nonzero _ hr _))

theorem branchValue_algebraic (r : Fin 5 → ℂ) (hr : ∀ i, IsAlgebraic ℚ (r i)) (S : Partition) :
    IsAlgebraic ℚ (branchValue r S) :=
  (((differences_algebraic _ hr _).isIntegral.mul
    (differences_algebraic _ hr _).isIntegral).pow 2).isAlgebraic

/-- Send the last of the six roots to infinity by x ↦ 1/(x−r₅). -/
def finiteBranches (r : Fin 6 → ℂ) (i : Fin 5) : ℂ := (r i.castSucc - r (Fin.last 5))⁻¹

theorem finiteBranches_injective {r : Fin 6 → ℂ} (hr : Function.Injective r) :
    Function.Injective (finiteBranches r) := by
  intro i j h
  exact Fin.castSucc_injective _ (hr (sub_left_inj.mp (inv_injective h)))

theorem finiteBranches_algebraic {r : Fin 6 → ℂ} (hr : ∀ i, IsAlgebraic ℚ (r i)) :
    ∀ i, IsAlgebraic ℚ (finiteBranches r i) := fun i =>
  ((hr i.castSucc).isIntegral.sub (hr (Fin.last 5)).isIntegral).isAlgebraic.inv

theorem sextic_root_algebraic {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {a : ℂ} (ha : aeval a (sextic u δ) = 0) : IsAlgebraic ℚ a := by
  refine ⟨sextic u δ, ?_,ha⟩
  intro h
  have hd := (smooth_sextic hu hδ).1
  simp [h] at hd

/-- Every admissible affine model has exactly six complex branch points. -/
theorem six_roots {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) :
    ∃ r : Fin 6 → ℂ, Function.Injective r ∧ ∀ i, aeval (r i) (sextic u δ) = 0 := by
  classical
  let f := sextic u δ
  obtain ⟨hd, hdisc⟩ := smooth_sextic hu hδ
  have hpos : 0 < f.natDegree := by change 0 < (sextic u δ).natDegree; omega
  have hf : f ≠ 0 := fun h => Nat.ne_of_gt hpos (by simp [h])
  have hres : resultant f f.derivative ≠ 0 := by
    rw [natDegree_derivative, resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hf)) hdisc
  have hsep : f.Separable := by
    change IsCoprime f f.derivative
    by_contra h
    exact hres (resultant_eq_zero_iff.mpr ⟨Or.inl hf,h⟩)
  have hcard : Fintype.card (f.rootSet ℂ) = 6 :=
    (card_rootSet_eq_natDegree (K := ℂ) hsep (IsAlgClosed.splits _)).trans hd
  let e := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => (e i : ℂ), Subtype.val_injective.comp e.injective,
    fun i => aeval_eq_zero_of_mem_rootSet (e i).prop⟩

/-- The analytic input is one labelled first Thomae identity for the finite branches
of the specified sextic, after sending the sixth root to infinity. -/
def of_sextic_thomae {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {z : Tuple} (r : Fin 6 → ℂ) (distinct : Function.Injective r)
    (root : ∀ i, aeval (r i) (sextic u δ) = 0) (label : Fin 10 ≃ Partition) (scale : ℂˣ)
    (identity : ∀ i, z (evenIndices i)^8 = (scale:ℂ)*branchValue (finiteBranches r) (label i))
    (odd_zero : ∀ i, (¬ ∃ k, evenIndices k = i) → z i = 0) : EighthPowerData z where
  value i := branchValue (finiteBranches r) (label i)
  algebraic i := branchValue_algebraic _ (finiteBranches_algebraic
    (fun j => sextic_root_algebraic hu hδ (root j))) (label i)
  nonzero i := branchValue_nonzero _ (finiteBranches_injective distinct) (label i)
  scale := scale
  identity := identity
  odd_zero := odd_zero

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.differences_nonzero
#print axioms ZInQBlueprint.ThetaPeriod.differences_algebraic
#print axioms ZInQBlueprint.ThetaPeriod.finiteBranches_injective
#print axioms ZInQBlueprint.ThetaPeriod.finiteBranches_algebraic
#print axioms ZInQBlueprint.ThetaPeriod.sextic_root_algebraic
#print axioms ZInQBlueprint.ThetaPeriod.six_roots
#print axioms ZInQBlueprint.ThetaPeriod.of_sextic_thomae
