import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic

/-! Closed subgroups of a real circle and projections with finite kernel. -/
namespace Sun28.RealComponents
open Set Topology
open scoped Topology
noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- A closed subgroup of a real circle is finite or the full circle. -/
theorem closed_circle_cases (H : AddSubgroup Circle) (closed : IsClosed (H : Set Circle)) :
    Finite H ∨ H=⊤ := by
  by_cases dense : Dense (H : Set Circle)
  · exact Or.inr (SetLike.ext' (closed.closure_eq.symm.trans dense.closure_eq))
  · left
    rw [AddCircle.dense_addSubgroup_iff_ne_zmultiples] at dense
    push Not at dense
    obtain ⟨a,ha,rfl⟩ := dense
    exact finite_zmultiples.mpr (addOrderOf_ne_zero_iff.mp ha)

theorem closed_circle_locallyConnected (H : AddSubgroup Circle) (closed : IsClosed (H : Set Circle)) :
    LocallyConnectedSpace H := by
  rcases closed_circle_cases H closed with fin|rfl
  · let _ := fin
    let _ := (Set.toFinite (H : Set Circle)).isDiscrete
    infer_instance
  · let _ : LocallyConnectedSpace Circle :=
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).isCoinducing.locallyConnectedSpace
    exact (Homeomorph.Set.univ Circle).isOpenEmbedding.locallyConnectedSpace

/-- Local connectedness lifts through a local homeomorphism. -/
theorem locallyConnected_of_localHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace Y] {f : X → Y} (h : IsLocalHomeomorph f) : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x U hU
  obtain ⟨e,hx,_⟩ := h x
  let x' : e.source := ⟨x,hx⟩
  let _ : LocallyConnectedSpace e.source := e.isOpenEmbedding_restrict.locallyConnectedSpace
  obtain ⟨V,hVU,hV,hxV,hconn⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
    (inferInstance : LocallyConnectedSpace e.source) x' (Subtype.val ⁻¹' U)
    (continuous_subtype_val.continuousAt hU)
  refine ⟨Subtype.val '' V, ?_,e.open_source.isOpenEmbedding_subtypeVal.isOpenMap _ hV,⟨x',hxV,rfl⟩,
    hconn.image _ continuous_subtype_val.continuousOn⟩
  rintro _ ⟨u,hu,rfl⟩
  exact hVU hu

/-- A continuous surjective homomorphism from a compact group to a Hausdorff
locally connected group with finite kernel gives a locally connected domain. -/
theorem locallyConnected_of_finite_kernel {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [CompactSpace A]
    [T2Space A] [T2Space B] [LocallyConnectedSpace B]
    (f : A →+ B) (cont : Continuous f) (surj : Function.Surjective f) [Finite f.ker] :
    LocallyConnectedSpace A := by
  have quotient := cont.isClosedMap.isQuotientMap cont surj
  have cover := quotient.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (Set.toFinite (f.ker : Set A)).isDiscrete
  exact locallyConnected_of_localHomeomorph (cover.isLocalHomeomorph _ _)

end
end Sun28.RealComponents
#print axioms Sun28.RealComponents.closed_circle_cases
#print axioms Sun28.RealComponents.closed_circle_locallyConnected
#print axioms Sun28.RealComponents.locallyConnected_of_localHomeomorph
#print axioms Sun28.RealComponents.locallyConnected_of_finite_kernel
