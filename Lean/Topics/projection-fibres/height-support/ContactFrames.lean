import PrimeSupport
namespace ProjectionFibres.HeightSupport
open StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.Comparison
open WitnessTransfer WitnessTransfer.Local WitnessTransfer.Height IndependentIndices
open BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind

def eligible (p : Nat) (t : Rat) :=
  Prime p ∧ p∉exceptional ∧ StructuralHeights.Contact p (mobius t)

/-- Every eligible prime is at most the absolute value of the homogeneous quintic. -/
noncomputable def fullPrimes (t : Rat) : List Nat := by
  classical
  exact (List.range ((StructuralHeights.quintic (mobius t).1 (mobius t).2).natAbs+1)).filter
    (fun p=>decide (eligible p t))

theorem mem_fullPrimes (t : Rat) (p : Nat) : p∈fullPrimes t ↔ eligible p t := by
  classical
  simp only [fullPrimes,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    obtain ⟨hp,away,contact⟩:=h
    have good:=(exceptional_units hp away).1
    have odd:=(StructuralHeights.contact_iff_quintic hp good _ (primitive t)).mp contact
    have qnz:= (oddValue hp odd).1
    have nn : StructuralHeights.quintic (mobius t).1 (mobius t).2≠0 := fun eq=>qnz (by rw [eq];decide)
    have bound:=Nat.le_of_dvd (Int.natAbs_pos.mpr nn) (Int.ofNat_dvd_left.mp (StructuralHeights.odd_dvd odd))
    exact ⟨by omega,⟨hp,away,contact⟩⟩

theorem depths_at_contact84 (x : Fin 84→Rat) (f : ProjectionFibres.Comparison.Frame) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) {p : Nat} (member : p∈fullPrimes (slope x f))
    {K : Type} [Field K] (w : ExtensionPlace p K) {rho : K} (root : rho^2=2) :
    ∃ r : K, (r=rho ∨ r= -rho) ∧ (∀ s∈(f.data x).steps,w.deep (s.m:Int) (s.y.eval w r)) ∧
       TypedDepths w r (f.primary x) (f.alt x) (SquareGate.label (cell x 1)) := by
  obtain ⟨hp,away,hit⟩:=(mem_fullPrimes _ _).mp member
  obtain ⟨_,_,large,n17⟩:=exceptional_units hp away
  obtain ⟨odd,regular⟩:=physical_contact x f (fromZero_domain x marked active zero) hp away hit
  exact ratio_depths84 x marked active zero f hp large n17 w root odd regular

/-- Remaining realization of local integral and joined elliptic charts at a full-support prime. -/
structure AtContact (x : Fin 84→Rat) (f : ProjectionFibres.Comparison.Frame) (p : Nat) (m : Int) (ns : Labels) where
  K : Type
  [fieldK : Field K]
  [charK : IsCharP K 0]
  w : ExtensionPlace p K
  rho : K
  root : rho^2=2
  charts : ∀ r : K, (r=rho ∨ r= -rho) →
    (∀ s∈(f.data x).steps,w.deep (s.m:Int) (s.y.eval w r)) →
    ∃ o : LocalSetup p K w, Nonempty (FourRows o x f m ns r)

def AtContact.geometry {x : Fin 84→Rat} {f : ProjectionFibres.Comparison.Frame} {p : Nat} {m : Int} {ns : Labels}
    (s : AtContact x f p m ns) (dom : domain x) (member : p∈fullPrimes (slope x f)) : GeometryAt x f p m ns := by
  obtain ⟨hp,away,hit⟩:=(mem_fullPrimes _ _).mp member
  obtain ⟨_,_,large,n17⟩:=exceptional_units hp away
  obtain ⟨odd,regular⟩:=physical_contact x f dom hp away hit
  exact @GeometryAt.mk x f p m ns s.K s.fieldK s.charK s.w s.rho s.root hp large n17 odd regular s.charts

/-- A frame of the active physical zero with its complete geometric contact set. -/
noncomputable def fullComparison (x : Fin 84→Rat) (f : ProjectionFibres.Comparison.Frame) (ns : Labels) (dom : domain x) (m : Int)
    (charts : ∀p∈fullPrimes (slope x f), Nonempty (AtContact x f p m ns))
    (ceiling : Nat) (height : ceiling≤detectorConstant*(radical (fullPrimes (slope x f)))^17+2) :
    ComparisonGeometry x f ns :=
  ⟨m,fullPrimes (slope x f),fun p member=>(charts p member).elim (fun d=>⟨d.geometry dom member⟩),ceiling,height⟩

def scalarEligible (p : Nat) (B : Rat) :=
  StructuralHeights.Prime p ∧ ¬(p:Int)∣210 ∧ p≠17 ∧
    StructuralHeights.Contact p (StructuralHeights.coordinates B)

/-- The complete scalar support for an argument B and the five-prime exceptional set. -/
noncomputable def scalarFullPrimes (B : Rat) : List Nat := by
  classical
  let q:=StructuralHeights.coordinates B
  exact (List.range ((StructuralHeights.quintic q.1 q.2).natAbs+1)).filter
    (fun p=>decide (scalarEligible p B))

theorem mem_scalarFullPrimes (B : Rat) (p : Nat) : p∈scalarFullPrimes B ↔
    StructuralHeights.Prime p ∧ ¬(p:Int)∣210 ∧ p≠17 ∧
      StructuralHeights.Contact p (StructuralHeights.coordinates B) := by
  classical
  simp only [scalarFullPrimes,List.mem_filter,List.mem_range,decide_eq_true_eq,scalarEligible]
  constructor
  · exact And.right
  · intro h
    obtain ⟨hp,away,n17,contact⟩:=h
    let q:=StructuralHeights.coordinates B
    have odd:=(StructuralHeights.contact_iff_quintic hp away q (StructuralHeights.coordinates_primitive B)).mp contact
    have qnz:= (oddValue hp odd).1
    have nn : StructuralHeights.quintic q.1 q.2≠0 := fun eq=>qnz (by rw [eq];decide)
    have bound:=Nat.le_of_dvd (Int.natAbs_pos.mpr nn) (Int.ofNat_dvd_left.mp (StructuralHeights.odd_dvd odd))
    exact ⟨Nat.lt_succ_of_le bound,hp,away,n17,contact⟩

theorem fullScalarContacts84 (x : Fin 84→Rat) (m n : Int)
    (charts : ∀p∈scalarFullPrimes (SquareGate.label (cell x 1)), HasLocalScalarCharts p x m n) :
    EvaluatedContacts x m n (scalarFullPrimes (SquareGate.label (cell x 1))) := by
  intro p member
  obtain ⟨hp,good,_,hit⟩:=(mem_scalarFullPrimes _ _).mp member
  exact ⟨hp,good,hit,charts p member⟩

#print axioms physical
#print axioms noMark
#print axioms primitive
#print axioms represents
#print axioms height_change
#print axioms physical_contact
#print axioms mem_fullPrimes
#print axioms depths_at_contact84
#print axioms AtContact.geometry
#print axioms fullComparison
#print axioms mem_scalarFullPrimes
#print axioms fullScalarContacts84
end ProjectionFibres.HeightSupport
