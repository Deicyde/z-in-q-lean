import RatioDepths
namespace ProjectionFibres.Comparison
open StructuralReduction StructuralReduction.Transfer84 BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- A single chosen conjugate simultaneously realizes every ratio comparison,
the input defect and the Lucas defect at one frame of the literal zero. -/
theorem ratio_depths84 (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (f : Frame) {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {K : Type} [Field K] (w : ExtensionPlace p K) {rho : K} (root : rho^2=2)
    (odd : OddOrder (order p (f.data x).R)) (regular : 0≤order p (f.data x).delta) :
    ∃ r : K, (r=rho ∨ r= -rho) ∧ (∀ s∈(f.data x).steps,w.deep (s.m:Int) (s.y.eval w r)) ∧
       TypedDepths w r (f.primary x) (f.alt x) (IndependentIndices.SquareGate.label (cell x 1)) := by
  obtain ⟨_,r,sg,all⟩:=comparison_depths84 x marked active zero f hp large away w root odd regular
  have rt : r^2=2 := by rcases sg with e|e <;> rw [e] <;> grobner
  have dom:=fromZero_domain x marked active zero
  refine ⟨r,sg,all,?_⟩
  cases f with
  | first => exact typed0 x dom w r rt all
  | second => exact typed1 x dom w r rt all
  | third => exact typed2 x dom w r rt all

#print axioms physicalLabel
#print axioms ratio_depths84
end ProjectionFibres.Comparison
