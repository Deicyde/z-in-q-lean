import CircuitLabels
import AnchorCollision

namespace EllipticOrbit.SignedLabels
open EllipticOrbit.Field
open PhysicalProjection.Comparison (Q2 times)
open EllipticHeight EllipticHeight.Labels
open ProjectionFibres ProjectionFibres.Actual

/-- The image of the signed quartic is the set of nonzero multiples of the marked point. -/
theorem signed_point_iff (group : Generated) (Q : Point) :
    SignedPoint Q ↔ ∃! n : ℤ, n≠0 ∧ Q=n • P := by
  constructor
  · rintro ⟨h,j,chart,rfl⟩
    obtain ⟨n,nz,point⟩ := chart_label group chart
    exact ⟨n,⟨nz,point⟩,fun _ hm => index_injective (hm.2.symm.trans point)⟩
  · rintro ⟨n,⟨nz,rfl⟩,_⟩
    apply (zsmul_P_signed n).resolve_left
    intro zero
    apply nz
    apply index_injective
    simpa only [zero_zsmul] using zero

/-- The prohibited pair in the two stored coordinates is exactly Mathlib's marked P. -/
theorem second_ne_generator {y : Fin 80 → Rat} (zero : Binding.V y 9813=0) :
    chartPoint (physical_root_charts y zero 1).1≠P := by
  let h:=rootH (decoded y) 1
  let j:=rootJ (decoded y) 1
  intro collision
  have pair:=(congrArg coordinates collision).trans P_pair
  change some ((ofPair h)^2,ofPair h*ofPair j)=
      some (ofPair (57/8,-7/2),ofPair (-165/8,417/32)) at pair
  have x:=congrArg Prod.fst (Option.some.inj pair)
  have ycoord:=congrArg Prod.snd (Option.some.inj pair)
  have xx : PhysicalProjection.Comparison.sq h=(57/8,-7/2) := ofPair_injective ((ofPair_sq h).trans x)
  have yy : times h j=(-165/8,417/32) := ofPair_injective ((ofPair_mul h j).trans ycoord)
  have markedX : ((57/8,-7/2):Q2)=PhysicalProjection.Comparison.sq ((-1,7/4):Q2) := by decide +kernel
  have markedY : ((-165/8,417/32):Q2)=times ((-1,7/4):Q2) (39/8,-9/2) := by decide +kernel
  apply AnchorCollision.excludes_P80 y zero
  exact ⟨xx.trans markedX,yy.trans markedY⟩

theorem actual_offset {y : Fin 80 → Rat} (zero : Binding.V y 9813=0) {n : ℤ}
    (point : chartPoint (physical_root_charts y zero 1).1=n • P) : n-1≠0 := by
  intro dead
  have one : n=1 := by omega
  exact second_ne_generator zero (by simpa only [one,one_zsmul] using point)

/-- Source-to-group statement for an ordinary zero, including the nonzero scalar
    offset, the exact represented fractions, and the two literal anchor denominators. -/
theorem physical_anchored_labels (group : Generated) {y : Fin 80 → Rat} (zero : Binding.V y 9813=0)
    : ∃ s : IndependentIndices.Labels, (∀ f : RootFractions y, PhysicalLabelling f s) ∧
      (∀ i, label s i≠0 ∧ ∀ k : ℤ, chartPoint (physical_root_charts y zero i).1=k • P ↔ k=label s i) ∧
      s.n₂-1≠0 ∧ ¬ 2∣(AnchorCircuit.parameter (decoded y)).den ∧
        ¬ 3∣(AnchorCircuit.parameter (decoded y)).den := by
  obtain ⟨s,_,labels⟩:=physical_labelling group zero (reducedRoots y)
  have represented (f : RootFractions y) : PhysicalLabelling f s := by
    obtain ⟨t,rep,ht⟩:=physical_labelling group zero f
    intro i
    have same : label t i=label s i := ((labels i).2 _).mp (((ht i).2 _).mpr rfl)
    have r:=rep i
    rw [same] at r
    exact r
  have point:=((labels 1).2 s.n₂).mpr rfl
  exact ⟨s,represented,labels,actual_offset zero point,AnchorCircuit.physical_anchor y zero⟩

end EllipticOrbit.SignedLabels

#print axioms EllipticOrbit.SignedLabels.signed_point_iff
#print axioms EllipticOrbit.SignedLabels.second_ne_generator
#print axioms EllipticOrbit.SignedLabels.actual_offset
#print axioms EllipticOrbit.SignedLabels.physical_anchored_labels
