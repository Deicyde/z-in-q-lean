import DetectorFrames
import DepthTheorem

namespace ProjectionFibres.Comparison
open StructuralReduction StructuralReduction.Transfer84 BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

def Frame.b (x : Fin 84→Rat) (f : Frame) : Rat := atWire x f.bN/atWire x f.bD
theorem literal_coefficient (x : Fin 84→Rat) (h : domain x) (f : Frame) :
    f.b x*(f.data x).trace^2=(f.data x).R := by
  have eq:=coefficient_relation (safe_bD x h f) (safe_rD x h f) (safe_tD x h f)
    (fractionN x f) (fractionD x f)
  cases f <;> dsimp only [Frame.b,Frame.bN,Frame.bD,Frame.rN,Frame.rD,Frame.tN,Frame.tD,Frame.data,data0,data1,data2,Data.trace] at eq ⊢ <;> exact eq

/-- All sixteen orders hold on one sign for each frame of the single physical assignment. -/
theorem comparison_depths84 (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (f : Frame) {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {K : Type} [Field K] (w : ExtensionPlace p K) {rho : K} (root : rho^2=2)
    (odd : OddOrder (order p (f.data x).R)) (regular : 0≤order p (f.data x).delta) :
    0<order p (f.data x).R ∧ ∃ r : K, (r=rho ∨ r= -rho) ∧
      ∀ s∈(f.data x).steps, w.deep (s.m:Int) (s.y.eval w r) := by
  have h:=fromZero_domain x marked active zero
  exact rawDepths hp large away w root (f.data x) (actualDetector x h f) (f.b x)
    (fraction_nonzero (safe_bN x h f) (safe_bD x h f)) (physicalPole x marked active zero f)
    (literal_coefficient x h f) odd regular

#print axioms signed_zero
#print axioms representation_ext
#print axioms fromZero_domain
#print axioms halfPoints
#print axioms physicalPole
#print axioms actualDetector
#print axioms literal_coefficient
#print axioms comparison_depths84
end ProjectionFibres.Comparison
