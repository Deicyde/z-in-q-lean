import RealScalarRatio

/-! Affine embedding of signed multiples in each real elliptic curve and finite
exceptional fibers in any finite list of translated, nonzero signed multiples. -/
namespace Sun28.RealRatio
open Set ZInQ WeierstrassCurve.Affine Sun28.WitnessIndices Sun28.Scalar
noncomputable section

abbrev PaperPoint := (curve (-(3-sqrt2)^2)).Point

def paperMultiple (m : ℤ) : PaperPoint := m • paperGenerator sqrt2_sq

theorem multiple_injective : Function.Injective paperMultiple := by
  intro a b same
  apply index_injective
  apply scalarEquiv.injective
  simpa only [scalar_index,paperMultiple] using same

abbrev EmbeddedPoint (σ : K0 →+* ℝ) := ((curve (-(3-sqrt2)^2)).map σ).Point

def embedded (σ : K0 →+* ℝ) : PaperPoint → EmbeddedPoint σ
  | .zero => .zero
  | .some x y h => .some (σ x) (σ y) (((curve _).map_nonsingular σ.injective x y).2 h)

theorem embedded_injective (σ : K0 →+* ℝ) : Function.Injective (embedded σ) := by
  intro P Q eq
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h => exact (Point.some_ne_zero _ eq.symm).elim
  | some x y h =>
    cases Q with
    | zero => exact (Point.some_ne_zero _ eq).elim
    | some u v h' =>
      have e := Point.some.inj eq
      rw [Point.some.injEq]
      exact ⟨σ.injective e.1,σ.injective e.2⟩

def realParameter (σ : K0 →+* ℝ) : EmbeddedPoint σ → ℝ
  | .zero => 0
  | .some x y _ => -x/y

theorem real_parameter_agrees (σ : K0 →+* ℝ) (P : PaperPoint) :
    realParameter σ (embedded σ P)=σ (parameter P) := by
  cases P <;> simp [embedded,realParameter,parameter]

/-- The image of the orbit in each real factor is infinite, without any
claim that the two factors vary independently. -/
theorem each_projected_orbit_infinite (σ : K0 →+* ℝ) :
    (Set.range fun h : ℤ => embedded σ (paperMultiple h)).Infinite :=
  Set.infinite_range_of_injective ((embedded_injective σ).comp multiple_injective)

/-- Each target finset lives on its own embedded curve, so conjugate and
translated exceptions may all be specified simultaneously. -/
theorem embedded_exceptions_finite {I : Type*} [Finite I] (σ : I→K0 →+* ℝ)
    (b c : I→ℤ) (nb : ∀ i,b i≠0)
    (target : ∀ i,Set (EmbeddedPoint (σ i))) (fin : ∀ i,(target i).Finite) :
    (⋃ i,(fun h : ℤ=>embedded (σ i) (paperMultiple (b i*(h-c i)))) ⁻¹' target i).Finite := by
  apply Set.finite_iUnion
  intro i
  apply (fin i).preimage
  apply Function.Injective.injOn
  intro h h' e
  have v:=multiple_injective (embedded_injective (σ i) e)
  have z:=mul_left_cancel₀ (nb i) v
  omega

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- A concrete sufficient adapter: continuous elliptic projections and the
real affine chart at the identity and at the actual signed multiples. -/
def parameterModel_of_projections (a : Orbit G)
    [∀ s : Bool,TopologicalSpace (EmbeddedPoint (place s))]
    (π : ∀ s : Bool,G→EmbeddedPoint (place s))
    (pcont : ∀ s,Continuous (π s))
    (orbit : ∀ s (m : ℤ),π s (m • a.generator)=embedded (place s) (paperMultiple m))
    (at_origin : ∀ s,ContinuousAt (realParameter (place s)) 0)
    (at_affine : ∀ s (m : ℤ),m≠0 →
      ContinuousAt (realParameter (place s)) (embedded (place s) (paperMultiple m))) :
    ParameterModel a where
  z s := realParameter (place s) ∘ π s
  value s m := by
    change realParameter (place s) (π s (m • a.generator))=_
    rw [orbit,real_parameter_agrees]
    rfl
  zero_continuous s := by
    have y : π s 0=0 := by simpa [paperMultiple,embedded,Point.zero_def] using orbit s 0
    exact (y ▸ at_origin s).comp (pcont s).continuousAt
  affine_continuous s m live := (orbit s m ▸ at_affine s m live).comp (pcont s).continuousAt


/-- Choose c before the integer targets b and translates are fixed. Then find one
H in any prescribed nonconstant progression, simultaneously omitting all of
those real exceptional points and satisfying strict inequalities at all places. -/
theorem choose_and_avoid (a : Orbit G) (model : ParameterModel a) (D : ℕ) (dp : 0<D) (cmin : ℤ) :
    ∃ (c : ℤ) (u : ℕ),c=(D:ℤ)*u ∧ max cmin 0<c ∧
    ∀ {I : Type} [Finite I] (σ : I→K0 →+* ℝ) (b j : I→ℤ) (_nb : ∀ i,b i≠0)
      (target : ∀ i,Set (EmbeddedPoint (σ i))) (_fin : ∀ i,(target i).Finite)
      (h₀ : ℤ) (L : ℕ) (_lp : 0<L) (hmin : ℤ),
      ∃ (h : ℤ) (k : ℕ),h=h₀+(L:ℤ)*k ∧ max hmin 0<h ∧
        (∀ i, embedded (σ i) (paperMultiple (b i*(h-j i)))∉target i) ∧
        (∀ τ : K0 →+* ℝ, |τ (zAt c)| < |τ (zAt h)|) ∧
        ∀ ν : NumberField.InfinitePlace K0,ν (zAt c)<ν (zAt h) := by
  obtain ⟨_,_,s⟩:=choose_real_indices a model
  obtain ⟨c,u,eq,hb,_,rest⟩:=s D dp cmin
  refine ⟨c,u,eq,hb,?_⟩
  intro I inst σ b j nb target fin h₀ L lp hmin
  obtain ⟨h,k,he,hl,out,hr,hv⟩:=rest h₀ L lp _ (embedded_exceptions_finite σ b j nb target fin) hmin
  exact ⟨h,k,he,hl,(fun i mem => out (Set.mem_iUnion.mpr ⟨i,mem⟩)),hr,hv⟩

end
end Sun28.RealRatio
#print axioms Sun28.RealRatio.multiple_injective
#print axioms Sun28.RealRatio.embedded_injective
#print axioms Sun28.RealRatio.real_parameter_agrees
#print axioms Sun28.RealRatio.each_projected_orbit_infinite
#print axioms Sun28.RealRatio.embedded_exceptions_finite
#print axioms Sun28.RealRatio.choose_and_avoid

#print axioms Sun28.RealRatio.parameterModel_of_projections
