import GeneratorRange
import NumeratorEndpoint

namespace Candidate80
open EllipticOrbit.Field
open EllipticHeight EllipticHeight.Labels
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.HeightSupport ProjectionFibres.Comparison
open HeightSpecialization IndependentIndices IndependentIndices.Assembly

/-- Both scalar coordinates and the 78 retained coordinates belong to the same rational point. -/
def JointFibre (t : ℚ) : Prop :=
  ∃ B : Base, B 0=t ∧ ∃ u v : ℚ, NewPoint (data B) u v

/-- Integer completeness and half-line soundness of the literal ordinary circuit. -/
def NaturalFibres : Prop := ∀ n : ℕ, JointFibre (n:ℚ)

def HalfSoundness : Prop := ∀ t : ℚ, 0≤2*t+1 → circuitImage false t → InputRestriction.IsInteger t

theorem ordinary_iff_joint (t : ℚ) : circuitImage false t ↔ JointFibre t := by
  constructor
  · rintro ⟨y,hy,hz⟩
    refine ⟨base80 y,hy,y 78,y 79,(reduced_iff ..).mp ?_⟩
    exact (Binding.ordinary_pointwise y).symm.trans hz
  · rintro ⟨B,input,u,v,rows⟩
    let y := pack80 B u v
    have fixed : base80 y=B := by
      funext i
      simp [y,base80,pack80,i.isLt]
    refine ⟨y,input,(Binding.ordinary_pointwise y).trans ?_⟩
    change squares (reducedRows (base80 y) u v)=0
    rw [fixed]
    exact (reduced_iff ..).mpr rows

theorem literal_criterion (marked : Bool) :
    (∀ t, circuitImage marked t ↔ InputRestriction.IsInteger t) ↔ NaturalFibres ∧ HalfSoundness := by
  rw [circuit_defines_iff]
  constructor
  · rintro ⟨complete,sound⟩
    exact ⟨fun n=>(ordinary_iff_joint _).mp (complete n),sound⟩
  · rintro ⟨complete,sound⟩
    exact ⟨fun n=>(ordinary_iff_joint _).mpr (complete n),sound⟩

/-- Literal signed coordinates corresponding to the four labels, including their nonvanishing. -/
def Marks (y : Fin 80→ℚ) (zero : Binding.V y 9813=0) (s : IndependentIndices.Labels) : Prop :=
  ∀ i, label s i≠0 ∧ chartPoint (physical_root_charts y zero i).1=label s i • EllipticOrbit.Field.P

theorem exists_marks (certificate : DoubledRange) (y : Fin 80→ℚ) (zero : Binding.V y 9813=0) :
    ∃ s, Marks y zero s := by
  obtain ⟨n,h,_,_,_⟩:=physical_labels_of_range certificate y zero
  let s : IndependentIndices.Labels:=⟨n 0,n 1,n 2,n 3⟩
  have labels (i : Fin 4) : label s i=n i := by fin_cases i <;> rfl
  exact ⟨s,fun i=>by rw [labels]; exact h i⟩

/-- Choose the signed labels before forming any of the three height or local conditions. -/
noncomputable def signedMarks (certificate : DoubledRange) (y : Fin 80→ℚ)
    (zero : Binding.V y 9813=0) : IndependentIndices.Labels :=
  Classical.choose (exists_marks certificate y zero)

theorem marks_spec (certificate : DoubledRange) (y : Fin 80→ℚ) (zero : Binding.V y 9813=0) :
    Marks y zero (signedMarks certificate y zero) :=
  Classical.choose_spec (exists_marks certificate y zero)

private theorem label_ext {s t : IndependentIndices.Labels}
    (same : ∀ i, label s i=label t i) : s=t := by
  cases s
  cases t
  simp only [IndependentIndices.Labels.mk.injEq]
  exact ⟨same 0,same 1,same 2,same 3⟩

theorem marks_unique {y : Fin 80→ℚ} {zero : Binding.V y 9813=0}
    {s t : IndependentIndices.Labels} (a : Marks y zero s) (b : Marks y zero t) : s=t := by
  exact label_ext (fun i=>signed_index_injective ((a i).2.symm.trans (b i).2))

def ComparisonPlaces (y : Fin 80→ℚ) (s : IndependentIndices.Labels) : Prop :=
  ∀ p∈fullPrimes (slope (decoded y) (tallest (decoded y))),
    Nonempty (SourcePlace (decoded y) (tallest (decoded y)) p s)

def ComparisonHeight (y : Fin 80→ℚ) : Prop :=
  SlopeHeight (decoded y) (tallest (decoded y))

def ScalarEstimate (y : Fin 80→ℚ) (s : IndependentIndices.Labels) : Prop :=
  ScalarCondition (decoded y) s.n₂

/-- A single primitive factor at an index of greatest absolute value. -/
def NumeratorEstimate (y : Fin 80→ℚ) (s : IndependentIndices.Labels) : Prop :=
  ∃ g : PrimitiveFactor (decoded y) s,
    (41^((label s g.row).natAbs^2))^2≤(QuadraticInt.norm g.a).natAbs

theorem selected_numerator {y : Fin 80→ℚ} (zero : Binding.V y 9813=0)
    {s : IndependentIndices.Labels} (points : Marks y zero s)
    (localPlaces : ComparisonPlaces y s) (slopeHeight : ComparisonHeight y)
    (numerator : NumeratorEstimate y s) :
    ∃ g : NumeratorData (decoded y), g.labels=s ∧
      (41^((label g.labels g.factor.row).natAbs^2))^2≤(QuadraticInt.norm g.factor.a).natAbs := by
  obtain ⟨odd,offset,divides⟩:=Prime23.Physical.index_conditions (n:=label s) zero points
  obtain ⟨factor,growth⟩:=numerator
  have modulus : (anchorModulus : ℤ)=(2:ℤ)*3^1474 := by
    simp only [anchorModulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact ⟨⟨s,localPlaces,factor,slopeHeight,odd 0,(points 3).1,offset,modulus.symm ▸ divides⟩,rfl,growth⟩

/-- A single physical point supplies all the local data and estimates at this stage. -/
def SelectedEstimates (certificate : DoubledRange) : Prop :=
  ∀ t : ℚ, 0≤2*t+1 → t≠0 → circuitImage false t →
    ∃ (y : Fin 80→ℚ) (zero : Binding.V y 9813=0), y 0=t ∧
      let s:=signedMarks certificate y zero
      ComparisonPlaces y s ∧ ComparisonHeight y ∧ ScalarEstimate y s ∧ NumeratorEstimate y s

/-- Soundness at one literal zero, with no completeness or generator hypothesis. -/
theorem integral_at_marked_zero {y : Fin 80→ℚ} (zero : Binding.V y 9813=0)
    {s : IndependentIndices.Labels} (points : Marks y zero s)
    (places : ComparisonPlaces y s) (height : ComparisonHeight y)
    (scalar : ScalarEstimate y s) (numerator : NumeratorEstimate y s) :
    InputRestriction.IsInteger (y 0) := by
  obtain ⟨g,repr,growth⟩:=selected_numerator zero points places height numerator
  have ordinary:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans zero)
  have domain:=fromZero_domain (decoded y) false (by simp) ordinary
  let d:=g.integer domain (q:=41) (by decide) growth
  have sc : ScalarCondition (decoded y) d.labels.n₂ := by
    change ScalarCondition (decoded y) g.labels.n₂
    rw [repr]
    exact scalar
  simpa only [input_decoded] using selected_integral ordinary (d.selected ordinary sc)

theorem half_sound_of_estimates (certificate : DoubledRange) (estimates : SelectedEstimates certificate) :
    HalfSoundness := by
  intro t side ht
  by_cases nz : t=0
  · exact ⟨0,nz⟩
  obtain ⟨y,zero,input,places,height,scalar,numerator⟩:=estimates t side nz ht
  rw [←input]
  exact integral_at_marked_zero zero (marks_spec certificate y zero) places height scalar numerator

theorem circuit_defines_of_estimates (marked : Bool) (certificate : DoubledRange)
    (fibres : NaturalFibres) (estimates : SelectedEstimates certificate) :
    ∀ t, circuitImage marked t ↔ InputRestriction.IsInteger t :=
  (literal_criterion marked).mpr ⟨fibres,half_sound_of_estimates certificate estimates⟩

#print axioms ordinary_iff_joint
#print axioms literal_criterion
#print axioms exists_marks
#print axioms marks_unique
#print axioms selected_numerator
#print axioms integral_at_marked_zero
#print axioms half_sound_of_estimates
#print axioms circuit_defines_of_estimates
end Candidate80
