import PaperDeckAction
import RamificationParameter
/-! The fixed sections of the deck map are exactly the six finite roots. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover MarkedForm CurveChart
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type) [Field K] [CharZero K]

abbrev fixedSections (u : ℚ) :=
  { m : Sections K (paperModel K u) // m ≫ (paperDeck u).hom = m }

def rootSection (u : ℚ) (a : {x : K // (paper K u false).IsRoot x}) :
    fixedSections K u :=
  ⟨chartSection _ _ (paper_overlap K u) false (branchCoords _ a.1 a.2),
    (chart_fixed_iff _ _ (paper_overlap K u) false _).2 rfl⟩

theorem rootSection_bijective {u : ℚ} (hu : u∉ZInQ.contactSet) :
    Function.Bijective (rootSection K u) := by
  constructor
  · intro x z e
    apply Subtype.ext
    have h := chartSection_injective _ _ (paper_overlap K u) false (congrArg Subtype.val e)
    exact congrArg (fun t => t.1.1) h
  · rintro ⟨m,hm⟩
    obtain ⟨p,hp⟩ := coordsSection_surjective _ _ (paper_overlap K u) m
    cases p with
    | inl a =>
      have he : chartSection _ _ (paper_overlap K u) false a = m := hp
      have ht : a.1.2 = 0 := (chart_fixed_iff _ _ (paper_overlap K u) false a).1 (he ▸ hm)
      have H : (paper K u false).IsRoot a.1.1 := by
        simpa [Polynomial.IsRoot,aeval_def, ht] using a.2.symm
      refine ⟨⟨a.1.1,H⟩,Subtype.ext (?_ : _ = m)⟩
      refine Eq.trans ?_ he
      apply congrArg (chartSection _ _ _ false)
      apply Subtype.ext
      exact Prod.ext rfl ht.symm
    | inr a =>
      have he : chartSection _ _ (paper_overlap K u) true (infinityCoord _ a) = m := hp
      have ht : a.1 = 0 := (chart_fixed_iff _ _ (paper_overlap K u) true (infinityCoord _ a)).1 (he ▸ hm)
      have hv : (aeval (0:K)) (paper K u true)=0 := by simp [←a.2,ht]
      exact (infinity_value_ne hu (by simpa only [paper_evaluate,ite_true] using hv)).elim

theorem finite_degree {u : ℚ} (hu : u∉ZInQ.contactSet) : (paper K u false).natDegree=6 := by
  let s := paperScale u (GlobalTwist.delta u : K)
  let t : K := (SexticIgusaChart.parameter u : K)
  have hs : s ≠ 0 := paperScale_ne hu (by exact_mod_cast (GlobalTwist.delta_pos u).ne')
  have id : paper K u false = C s * DirectCharts.monicSextic t := by
    apply Polynomial.funext
    intro x
    change (aeval x) (paper K u false) = _
    rw [paper_evaluate,F,paper_formula hu, eval_mul,eval_C,DirectCharts.monic_eval]
    rfl
  exact id ▸ (natDegree_C_mul hs).trans (DirectCharts.monic_six t).2

theorem fixed_count [IsAlgClosed K] {u : ℚ} (hu : u∉ZInQ.contactSet) :
    Nat.card (fixedSections K u) = 6 := by
  classical
  let f := paper K u false
  have hdeg : f.natDegree=6 := finite_degree K hu
  have hn : f ≠ 0 := fun h => by simp [h] at hdeg
  let e : {x : K // f.IsRoot x} ≃ (↑f.roots.toFinset : Type) :=
    Equiv.subtypeEquivProp (by funext x; simp [Polynomial.mem_roots hn])
  rw [←Nat.card_congr (Equiv.ofBijective _ (rootSection_bijective K hu)), Nat.card_congr e]
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,Multiset.toFinset_card_of_nodup
    (Polynomial.nodup_roots (paper_chart_regular K hu false).2),IsAlgClosed.card_roots_eq_natDegree,hdeg]
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.rootSection_bijective
#print axioms ZInQBlueprint.WeightedCurvePoints.fixed_count
