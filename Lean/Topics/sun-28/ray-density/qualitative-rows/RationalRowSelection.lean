import RationalOrders
import WindowAssembly

namespace Sun28.QualitativeRows
open IsDedekindDomain NumberField
open scoped NumberField
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.Scalar Sun28.WitnessIndices Sun28.ContactFactors Sun28.ScalarPlaces
open Sun28.GaussianSelection Sun28.Exceptional Sun28.SelectedTrace Sun28.RealRatio
open Sun28.PairedClasses Sun28.TwistRank Sun28.FiniteWitness Sun28.ContactSieve ManuscriptV15.Arithmetic
noncomputable section

open private scalar_ready' from SelectedPreparation
open private note_ray_norm from RaySelection

/-- All prime requirements are tests on one tuple of rational integers. The square
roots exist automatically because p is 1 modulo 16, and can be specified by any
deterministic choice when evaluating the two finite point counts. -/
def RationalRow {X : ℤ} (w : Window X) : Prop :=
  let A:=fixedScale w.n
  ∃ (u v : ℕ) (values : PrimeValues A u v),
    0<v ∧ requiredDivisor A∣v ∧ slopeThreshold A w.C (1/2)<(slope A u v:ℝ) ∧ RayValues values ∧
    (∀ j,∀ p∈selected values j,¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
    ∃ z : (i : ↥(shifts A))→ZMod (values.value i), (∀ i,(z i)^2=2) ∧
      ∀ j, ¬Walk (Edge (fun i s=>curveOrders (z i) s) (fixedMod (integerRadicand X))
        (fixedRes (integerRadicand X)) (Nat.factorial 576)) j j true

theorem rational_of_gaussian {X : ℤ} (w : Window X) (row : AdmitsRow w) : RationalRow w := by
  classical
  obtain ⟨u,v,values,π,vp,dv,large,big,ex,ray,balanced⟩:=row
  have roots (i : ↥(shifts (fixedScale w.n))) :
      ∃ z : ZMod (values.value i), z^2=2 ∧
      pointCount (values.value i) (-(3-z)^2)=adjacentNorm (π i) true ∧
      pointCount (values.value i) (-(3+z)^2)=adjacentNorm (π i) false := by
    let _ := Fact.mk (values.prime _ i.property)
    exact CMReduction.exists_oriented_root (ray.norm i) (ray.ray16 i) (ray.ray7 i)
  choose z sq plus minus using roots
  have eq : (fun i s=>curveOrders (z i) s)=(fun i s => adjacentNorm (π i) s) := by
    funext i s
    cases s
    · simpa only [curveOrders,Bool.false_eq_true,ite_false,sub_neg_eq_add] using minus i
    · exact plus i
  refine ⟨u,v,values,vp,dv,large,?_,ex,z,sq,?_⟩
  · intro d hd
    have r:=note_ray_norm (ray.ray16 ⟨d,hd⟩) (ray.ray7 ⟨d,hd⟩)
    rw [ray.norm] at r
    exact ⟨big d hd,r⟩
  · rw [eq];exact balanced

/-- The Gaussian norm and orientation conditions disappear from the premise
of the nine-point theorem. Only the rational residue and actual finite curves enter. -/
theorem selected_of_rational {X : ℤ} (window : Window X) (row : RationalRow window) :
    ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η := by
  obtain ⟨u,v,values,vp,dv,large,rays,ex,z,sq,balanced⟩:=row
  apply selected_of_progression window values vp dv large rays ex
  have nz i s : 0<curveOrders (z i) s := by unfold curveOrders pointCount;omega
  obtain ⟨x,b,L,pos,all⟩:=solve_at_orders (fun i s=>curveOrders (z i) s) _ nz balanced
  refine ⟨b,L,pos,fun k=>?_⟩
  obtain ⟨div,localRes,orders⟩:=all k
  refine ⟨div,localRes,?_⟩
  intro B rep j p sel
  have a0 : fixedScale window.n 0=1 := by norm_num [fixedScale,scaleRoot]
  have pos := actual_scales_positive window.n (fun i=>(window.roots.odd i).1.ne')
  have root : beta X=(window.n 0:ℚ) := by rw [window.roots.beta];simp [beta]
  exact (rational_trace values a0 (fun j=>(pos j).ne') vp z sq x (fun d hd=>(rays d hd).1) ex
    orders rep window.roots.lucas_eq root j p sel).2.1

theorem rational_preparation {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit)
    (rows : ∀ X, RationalRow (fixedWindow orbit model X)) (X : ℤ) :
    ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η :=
  selected_of_rational _ (rows X)

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.rational_of_gaussian
#print axioms Sun28.QualitativeRows.selected_of_rational
#print axioms Sun28.QualitativeRows.rational_preparation
