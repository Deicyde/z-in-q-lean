import CircleCovers

/-! Projection of a closed subgroup of a two-dimensional torus onto a circle. -/
namespace Sun28.RealComponents
open Set Topology
noncomputable section

private def first (H : AddSubgroup (Circle × Circle)) : H →+ Circle :=
  (AddMonoidHom.fst _ _).comp H.subtype

private def vertical (H : AddSubgroup (Circle × Circle)) : AddSubgroup Circle :=
  H.comap (AddMonoidHom.inr _ _)

private theorem vertical_finite_kernel (H : AddSubgroup (Circle × Circle))
    [Finite (vertical H)] : Finite (first H).rangeRestrict.ker := by
  let K := (first H).rangeRestrict.ker
  have zero (x : K) : x.1.1.1=0 :=
    congrArg ((↑) : (first H).range → Circle) x.2
  let embed (x : K) : vertical H := ⟨x.1.1.2,by
    change ((0:Circle),x.1.1.2)∈H
    rw [← zero x]
    exact x.1.2⟩
  apply Finite.of_injective embed
  intro x y same
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext ((zero x).trans (zero y).symm) (congrArg Subtype.val same)

private theorem full_vertical (H : AddSubgroup (Circle × Circle)) (full : vertical H=⊤)
    (x : (first H).range) (y : Circle) : (x.1,y)∈H := by
  obtain ⟨a,⟨u,rfl⟩⟩ := x
  have v : ((0:Circle),y-u.1.2)∈H := by
    change y-u.1.2∈vertical H
    rw [full]
    trivial
  change (u.1.1,y)∈H
  have eq : u.1+((0:Circle),y-u.1.2)=(u.1.1,y) := by
    ext <;> simp
  exact eq ▸ H.add_mem u.2 v

private def splitHomeomorph (H : AddSubgroup (Circle × Circle)) [CompactSpace H]
    (full : vertical H=⊤) : H ≃ₜ ((first H).range × Circle) := by
  let e : H ≃ (first H).range × Circle :=
    ⟨fun x => ((first H).rangeRestrict x,x.1.2),
     fun p => ⟨(p.1.1,p.2),full_vertical H full p.1 p.2⟩,fun _ => rfl,fun _ => rfl⟩
  apply Continuous.homeoOfEquivCompactToT2 (f:=e)
  exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)

/-- Every closed subgroup of the two-dimensional real torus is locally connected. -/
theorem closed_two_circles (H : AddSubgroup (Circle × Circle)) (closed : IsClosed (H : Set (Circle × Circle))) :
    LocallyConnectedSpace H := by
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp closed.isCompact
  have cont : Continuous (first H) := continuous_fst.comp continuous_subtype_val
  have image : IsClosed ((first H).range : Set Circle) := (isCompact_range cont).isClosed
  let _ := closed_circle_locallyConnected (first H).range image
  have vclosed : IsClosed (vertical H : Set Circle) :=
    closed.preimage (continuous_const.prodMk continuous_id : Continuous (fun y : Circle => ((0:Circle),y)))
  rcases closed_circle_cases (vertical H) vclosed with fin|full
  · let _ := fin
    let _ := vertical_finite_kernel H
    exact locallyConnected_of_finite_kernel _ (cont.subtype_mk _) (first H).rangeRestrict_surjective
  · let _ : LocallyConnectedSpace Circle :=
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).isCoinducing.locallyConnectedSpace
    exact (splitHomeomorph H full).isOpenEmbedding.locallyConnectedSpace

/-- A finite kernel suffices even when the image is a proper closed subgroup of the torus. -/
theorem locallyConnected_of_two_coordinates {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A]
    (f : A →+ Circle × Circle) (cont : Continuous f) [Finite f.ker] : LocallyConnectedSpace A := by
  let _ := closed_two_circles f.range ((isCompact_range cont).isClosed)
  have kernel : f.rangeRestrict.ker=f.ker := by ext x; simp
  let _ : Finite f.rangeRestrict.ker := kernel ▸ inferInstance
  exact locallyConnected_of_finite_kernel _ (cont.subtype_mk _) f.rangeRestrict_surjective

end
end Sun28.RealComponents
#print axioms Sun28.RealComponents.closed_two_circles
#print axioms Sun28.RealComponents.locallyConnected_of_two_coordinates
