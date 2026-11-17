import UniformUnitObstruction
import Mathlib.NumberTheory.Padics.Complex

/-! Existence of roots and of extending absolute values for the branch-unit counterexample. -/
open Polynomial
namespace ZInQBlueprint.BranchHeight.UnitObstruction
open SexticThetaHeight
noncomputable section

/-- Every smooth sextic of the family admits a labeling of its six complex roots. -/
theorem paper_roots {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) :
    ∃ r : Fin 6 → ℂ, Function.Injective r ∧ ∀ i, aeval (r i) (sextic u δ)=0 := by
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
    (card_rootSet_eq_natDegree (K:=ℂ) hsep (IsAlgClosed.splits _)).trans hd
  let e : Fin 6 ≃ f.rootSet ℂ := Fintype.equivOfCardEq (by simp [hcard])
  exact ⟨fun i => (e i).val,Subtype.val_injective.comp e.injective,
    fun i => aeval_eq_zero_of_mem_rootSet (e i).property⟩

/-- Restrict the norm of an algebraic closure of the p-adic field along an embedding. -/
theorem place_exists (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ∃ v : AbsoluteValue K ℝ, IsNonarchimedean v ∧ LiesOver p v := by
  let e : K →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  let v : AbsoluteValue K ℝ :=
    { toFun := fun x => ‖e x‖
      map_mul' := fun x y => by rw [map_mul,norm_mul]
      nonneg' := fun x => norm_nonneg _
      eq_zero' := fun x => by simp
      add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _ }
  refine ⟨v,?_,1,by norm_num,?_⟩
  · intro x y
    change ‖e (x+y)‖ ≤ max ‖e x‖ ‖e y‖
    rw [map_add]
    exact PadicAlgCl.isNonarchimedean p _ _
  · intro q
    change ‖e (q:K)‖ = _
    rw [map_ratCast,Real.rpow_one]
    calc ‖(q : PadicAlgCl p)‖
      _ = ‖((q:ℚ_[p]) : PadicAlgCl p)‖ := by rw [map_ratCast]
      _ = ‖(q:ℚ_[p])‖ := PadicAlgCl.norm_extends p _
      _ = _ := Padic.eq_padicNorm _

/-- Every finite S admits an actual branch configuration at a prime outside S and the
contact support. Its discriminant classes have even valuation, but a branch ratio is a nonunit. -/
theorem finite_set_counterexample (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∉ S ∧
      ¬p ∣ ZInQ.contactSupport S (parameterAt p) ∧
      Even (padicValRat p (rootClass₁ (parameterAt p))) ∧
      Even (padicValRat p (rootClass₂ (parameterAt p))) ∧
      Even (padicValRat p (rootClass₃ (parameterAt p))) ∧
      ∃ r : Fin 6 → ℂ, Function.Injective r ∧ (∀ i, aeval (r i) (sextic (parameterAt p) 1)=0) ∧
      ∃ v : AbsoluteValue (weightField r) ℝ, IsNonarchimedean v ∧ LiesOver p v ∧
      ∃ i : Fin 10, v (weights r i) ≠ 1 := by
  obtain ⟨p,hp,hl,hS,hs,h₁,h₂,h₃⟩ := outside_every_finite_set S
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,hr,hz⟩ := paper_roots (unmarked_at (p:=p)) (show (1:ℚ) ≠ 0 by norm_num)
  let := weight_numberField (unmarked_at (p:=p)) one_ne_zero hz
  obtain ⟨v,hv,hplace⟩ := place_exists p (weightField r)
  exact ⟨p,hp,hl,hS,hs,h₁,h₂,h₃,r,hr,hz,v,hv,hplace,uniform_paper_nonunit hl one_ne_zero hr hz v hv hplace⟩

/-- There is no labeling making every normalized branch coordinate a unit at every
place outside the conductor primes, even for the fixed public multiplication-prime set. -/
theorem public_conductor_counterexample :
    ∃ (u : ℚ) (p : ℕ), u ∉ ZInQ.contactSet ∧ p.Prime ∧
      p ∉ HeightBudget.conductorPrimes ZInQ.Mult.S_mul u ∧
      (∀ r : Fin 6 → ℂ, Function.Injective r → (∀ i, aeval (r i) (sextic u 1)=0) →
        ∃ v : AbsoluteValue (weightField r) ℝ, IsNonarchimedean v ∧ LiesOver p v ∧
        ∃ i, v (weights r i) ≠ 1) := by
  obtain ⟨p,hp,hl,hS,hs,_⟩ := outside_every_finite_set ZInQ.Mult.S_mul
  let : Fact p.Prime := ⟨hp⟩
  have hu := unmarked_at (p:=p)
  refine ⟨parameterAt p,p,hu,hp,?_,?_⟩
  · intro h
    rcases Finset.mem_union.mp h with hmem|hmem
    · exact hS hmem
    · exact hs (Nat.dvd_of_mem_primeFactors hmem)
  · intro r hr hz
    let := weight_numberField hu one_ne_zero hz
    obtain ⟨v,hv,hplace⟩ := place_exists p (weightField r)
    exact ⟨v,hv,hplace,uniform_paper_nonunit hl one_ne_zero hr hz v hv hplace⟩

end
end ZInQBlueprint.BranchHeight.UnitObstruction
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.paper_roots
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.place_exists
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.finite_set_counterexample
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.public_conductor_counterexample
