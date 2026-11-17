import ClosedCircleProducts
import RealProjection
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

/-! Specialization of circle subgroup structure to the actual diagonal elliptic orbit. -/
namespace Sun28.RealComponents
open ZInQ Sun28.RealRatio Sun28.RealCharts Sun28.RealProjection Sun28.CyclicOrbit
open scoped Sun28.RealCharts
noncomputable section

local instance : CompactSpace RealPair := compact_pair
local instance : T2Space RealPair := hausdorff_pair
local instance : IsTopologicalAddGroup RealPair := topological_pair

/-- The published real-group classification in the case of three distinct real roots. -/
def HusemollerModels : Prop := ∀ s : Bool, Nonempty (EmbeddedPoint (place s) ≃ₜ+ Circle × ZMod 2)

/-- On either real curve the cubic has the three distinct roots required by Husemöller. -/
theorem three_real_roots (σ : K0 →+* ℝ) :
    let d := σ (3-sqrt2)
    (∀ x : ℝ, x^3-d^2*x = x*(x-d)*(x+d)) ∧ d≠0 ∧ -d≠0 ∧ d≠-d := by
  let d := σ (3-sqrt2)
  have nz : d≠0 := by
    intro h
    have eq := σ.injective (h.trans σ.map_zero.symm)
    have e : sqrt2=(3:K0) := (sub_eq_zero.mp eq).symm
    have q := sqrt2_sq
    rw [e] at q
    norm_num at q
  exact ⟨fun x => by ring,nz,neg_ne_zero.mpr nz,fun eq => nz (by linarith)⟩

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B]

/-- Two circle coordinates with a finite kernel on the ambient product retain
a finite kernel upon restriction to every compact subgroup. -/
theorem finite_coordinates_on_subgroup {F : Type*} [Finite F]
    (π : A →+ Circle × Circle) (cont : Continuous π) (tag : A → F)
    (separates : Function.Injective (fun a => (π a,tag a)))
    (D : AddSubgroup A) [CompactSpace D] [IsTopologicalAddGroup A] [T2Space A] :
    LocallyConnectedSpace D := by
  let f := π.comp D.subtype
  let _ : Finite f.ker := Finite.of_injective (fun x : f.ker => tag x.1.1) (by
    intro x y eq
    apply Subtype.ext
    apply Subtype.ext
    apply separates
    exact Prod.ext (x.2.trans y.2.symm) eq)
  exact locallyConnected_of_two_coordinates f (cont.comp continuous_subtype_val)

/-- Both published circle models imply the remaining component assertion on the
literal closure of Sun's diagonal point. -/
theorem openComponent_of_husemoller (models : HusemollerModels) : OpenComponent := by
  obtain ⟨e⟩ := models false
  obtain ⟨s⟩ := models true
  let π : RealPair →+ Circle × Circle :=
    ((AddMonoidHom.fst _ _).comp e.toAddEquiv.toAddMonoidHom).prodMap
    ((AddMonoidHom.fst _ _).comp s.toAddEquiv.toAddMonoidHom)
  let tag (a : RealPair) := ((e a.1).2,(s a.2).2)
  have cont : Continuous π :=
    (continuous_fst.comp (e.continuous.comp continuous_fst)).prodMk
      (continuous_fst.comp (s.continuous.comp continuous_snd))
  have separates : Function.Injective (fun a => (π a,tag a)) := by
    intro x y eq
    have cs := congrArg Prod.fst eq
    have fs := congrArg Prod.snd eq
    have cx : (e x.1).1=(e y.1).1 := congrArg (fun p : Circle × Circle => p.1) cs
    have cy : (s x.2).1=(s y.2).1 := congrArg (fun p : Circle × Circle => p.2) cs
    have tx : (e x.1).2=(e y.1).2 := congrArg (fun p : ZMod 2 × ZMod 2 => p.1) fs
    have ty : (s x.2).2=(s y.2).2 := congrArg (fun p : ZMod 2 × ZMod 2 => p.2) fs
    exact Prod.ext (e.injective (Prod.ext cx tx)) (s.injective (Prod.ext cy ty))
  let _ := finite_coordinates_on_subgroup π cont tag separates DiagonalClosure
  exact open_of_locally_connected

theorem integer_definition_28 (models : HusemollerModels)
    (units : Sun28.FiveMarkUnits.PublishedCorollary72) (height : Sun28.MinimalConductors.ExactLeastHeight)
    (patterns : Sun28.NormSieve.PrimeValuesWithResidues) (twists : Sun28.PairedClasses.Residual) :
    Sun28.IntegerDefinition28 :=
  Sun28.RealProjection.integer_definition_28 (openComponent_of_husemoller models) units height patterns twists

end
end Sun28.RealComponents
#print axioms Sun28.RealComponents.three_real_roots
#print axioms Sun28.RealComponents.finite_coordinates_on_subgroup
#print axioms Sun28.RealComponents.openComponent_of_husemoller
#print axioms Sun28.RealComponents.integer_definition_28
