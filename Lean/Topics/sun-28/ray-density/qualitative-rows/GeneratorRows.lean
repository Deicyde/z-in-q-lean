import RationalRowSelection
import GeneratorTrace

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

def PointRow {X : ℤ} (w : Window X) : Prop :=
  let A:=fixedScale w.n
  ∃ (u v : ℕ) (values : PrimeValues A u v),
    0<v ∧ requiredDivisor A∣v ∧ slopeThreshold A w.C (1/2)<(slope A u v:ℝ) ∧ ∃ rays : RayValues values,
    (∀ j,∀ p∈selected values j,¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
    ∃ (z : (i : ↥(shifts A))→ZMod (values.value i)), ∃ sq : ∀ i,(z i)^2=2,
      ∀ j, ¬Walk (Edge (periodAt values (fun d h=>(rays d h).1) z sq) (fixedMod (integerRadicand X))
        (fixedRes (integerRadicand X)) (Nat.factorial 576)) j j true

/-- Decreasing the order at any coordinate only removes graph constraints. -/
theorem balanced_of_dvd {ι J : Type*} (large small : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ)
    (div : ∀ i s,small i s∣large i s)
    (bal : ∀ i,¬Walk (Edge large m r C) i i true) : ∀ i,¬Walk (Edge small m r C) i i true := by
  have grow {a b c d : ℕ} (ac : a∣c) (bd : b∣d) : a.gcd b ∣ c.gcd d :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left a b).trans ac) ((Nat.gcd_dvd_right a b).trans bd)
  have lift {u v d} (e : Constraint small m r C u v d) : Constraint large m r C u v d := by
    cases e with
    | pair i j s t bad =>
      apply Constraint.pair
      intro g
      exact bad ((grow (div i s) (div j t)).trans g)
    | pin j i s t bad =>
      apply Constraint.pin
      intro g
      exact bad (g.of_dvd (grow (dvd_refl (m j)) (div i s)))
  have liftEdge {u v d} (e : Edge small m r C u v d) : Edge large m r C u v d :=
    e.elim (fun h=>Or.inl (lift h)) (fun h=>Or.inr (lift h))
  have walk {i j b} (w : Walk (Edge small m r C) i j b) : Walk (Edge large m r C) i j b := by
    induction w with
    | nil => exact Walk.nil _
    | step w e ih => exact ih.step (liftEdge e)
  exact fun i w=>bal i (walk w)

/-- A point period divides the full finite-field cardinality at every selected
prime. No point count or Gaussian ray is required by the resulting test. -/
theorem point_of_rational {X : ℤ} (window : Window X) (row : RationalRow window) : PointRow window := by
  obtain ⟨u,v,values,vp,dv,large,rays,ex,z,sq,balanced⟩:=row
  refine ⟨u,v,values,vp,dv,large,rays,ex,z,sq,?_⟩
  exact balanced_of_dvd _ _ _ _ _ (periodAt_dvd values (fun d h=>(rays d h).1) z sq) balanced

theorem selected_of_point {X : ℤ} (window : Window X) (row : PointRow window) :
    ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η := by
  obtain ⟨u,v,values,vp,dv,large,rays,ex,z,sq,balanced⟩:=row
  apply selected_of_progression window values vp dv large rays ex
  let big:=fun d (hd : d∈shifts (fixedScale window.n)) => (rays d hd).1
  obtain ⟨x,b,L,pos,all⟩:=solve_at_orders (periodAt values big z sq) _ (periodAt_positive values big z sq) balanced
  refine ⟨b,L,pos,fun k=>?_⟩
  obtain ⟨div,localRes,orders⟩:=all k
  refine ⟨div,localRes,?_⟩
  intro B rep j p sel
  have a0 : fixedScale window.n 0=1 := by norm_num [fixedScale,scaleRoot]
  have pos := actual_scales_positive window.n (fun i=>(window.roots.odd i).1.ne')
  have root : beta X=(window.n 0:ℚ) := by rw [window.roots.beta];simp [beta]
  exact (period_trace values a0 (fun j=>(pos j).ne') vp z sq x (fun d hd=>(rays d hd).1) ex
    orders rep window.roots.lucas_eq root j p sel).2.1

theorem period_preparation {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Orbit G) (model : ParameterModel orbit)
    (rows : ∀ X, PointRow (fixedWindow orbit model X)) (X : ℤ) :
    ∃ a : Fin 9 → AffineInput, ∃ η : ℚ, SelectedAt (nineAffine a).doubles (X:ℚ) η :=
  selected_of_point _ (rows X)

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.balanced_of_dvd
#print axioms Sun28.QualitativeRows.point_of_rational
#print axioms Sun28.QualitativeRows.selected_of_point
#print axioms Sun28.QualitativeRows.period_preparation
