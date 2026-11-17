import Reflection
import IntegralComparisons
import Geometry84

namespace ProjectionFibres.Actual
open StructuralReduction StructuralReduction.Transfer84 WitnessTransfer.Height
open IndependentIndices IndependentIndices.Assembly BinaryQuartic ProgressionWitnesses.SingleContact
open ProjectionFibres.Comparison Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- The four removed coordinates are evaluated explicitly at a reduced witness. -/
def decoded (y : Fin 80→Rat) : Fin 84→Rat :=
  let B:=base80 y
  let f:=data B
  let a:=f.h*y 78
  let b:=f.h*y 79
  let q:=qnorm a b
  fill B a b (f.A/f.L) (f.M q/f.K) ((f.N q/f.D)/f.kappa) f.guard⁻¹

theorem input_decoded (y : Fin 80→Rat) : cell (decoded y) 1=y 0 := rfl

theorem ordinary_decoded (y : Fin 80→Rat) (z : output80 false y=0) :
    output false (decoded y)=0 := by
  let B:=base80 y
  let f:=data B
  have cond:= (reduced_iff B (y 78) (y 79)).mp z
  have nr : r (empty B)≠0 := by have := r_positive (empty B);grind
  have L0 : f.L≠0 := by change (r (empty B))^16≠0;grind
  have C0 : f.C≠0 := by change (r (empty B))^3≠0;grind
  have k0 : f.kappa≠0 := by change Wires.kappa≠0;decide
  exact (normal_form B _ _ _ _ _ _).mpr (lift cond L0 C0 k0)

structure CubicAt (p : Nat) (x : Fin 84→Rat) (m n : Int) where
  K : Type
  G : Type
  G' : Type
  [ground : Field K]
  [group : IntModule G]
  [group' : IntModule G']
  w : ExtensionPlace p K
  rho : K
  C : CubicGeometry ((3-rho)^2) G
  N : CubicGeometry ((3-(-rho))^2) G'
  left : ScalarSource w C.model m n (cell x 25) (cell x 26)
  right : ScalarSource w N.model m n (cell x 25) (cell x 26)
  leftF : left.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*rho
  rightF : right.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*(-rho)

structure ScalarGeometry (x : Fin 84→Rat) (n : Int) where
  m : Int
  primes : List Nat
  contact : ∀p∈primes, StructuralHeights.Prime p ∧ ¬(p:Int)∣210 ∧
    StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label (cell x 1))) ∧
    Nonempty (CubicAt p x m n)
  fiveMark : multiplicativeHeight (SquareGate.label (cell x 1))≤
    2^(2*scalarConstant*(radical primes)^17)

def ScalarGeometry.forces {x : Fin 84→Rat} {n : Int}
    (s : ScalarGeometry x n) (zero : output false x=0) : ScalarContacts (cell x 1) n := by
  refine ⟨s.primes,?_,?_,s.fiveMark⟩
  · intro p member
    obtain ⟨hp,good,_⟩:=s.contact p member
    rcases hp.2 _ (Nat.gcd_dvd_right 6 p) with h|h
    · exact h
    · have dvd : p∣6 := h ▸ Nat.gcd_dvd_left 6 p
      exact False.elim (good (Int.natCast_dvd_natCast.mpr (Nat.dvd_trans dvd (by decide : 6∣210))))
  · intro p member
    obtain ⟨hp,good,hit,⟨g⟩⟩:=s.contact p member
    letI:=g.ground
    letI:=g.group
    letI:=g.group'
    obtain ⟨hr,pos,odd⟩:=physical_contact_order hp good _ hit
    have away : p≠17 := by
      intro eq
      subst p
      exact StructuralHeights.no_contact_17 _ hit
    have large : 5≤p := by
      by_cases h : p=2 ∨ p=3
      · rcases h with rfl|rfl <;> exact False.elim (good (by decide))
      · have four : p≠4 := by
          rintro rfl
          have bad:=hp.2 2 (by decide)
          omega
        have min:=hp.1;omega
    exact source_scalar_divisor84 false x (by simp) zero g.C g.N hp large away hr pos odd
      g.left g.right g.leftF g.rightF

/-- Each comparison has its own primes, local field and common sign. The scalar
uses its two source points and the ordinary projective group law at each contact. -/
structure ArithmeticData (x : Fin 84→Rat) where
  labels : Labels
  first : ComparisonGeometry x .first labels
  second : ComparisonGeometry x .second labels
  third : ComparisonGeometry x .third labels
  scalar : ScalarGeometry x labels.n₂
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  anchorNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1
  abscissas : 2*(labelSize labels)^2 ≤ 15+3*largest first.slopeCeiling second.slopeCeiling third.slopeCeiling

theorem integer_of_arithmetic80 (mark : Bool) (y : Fin 80→Rat) (z : output80 mark y=0)
    (geometry : y 0≠0 → Nonempty (ArithmeticData (decoded y))) : InputRestriction.IsInteger (y 0) := by
  by_cases e : y 0=0
  · exact ⟨0,e⟩
  have zo : output80 false y=0 := by
    cases mark with
    | false=>exact z
    | true=>exact (Rat.mul_eq_zero.mp z).resolve_left e
  have zero:=ordinary_decoded y zo
  obtain ⟨g⟩:=geometry e
  exact (integral_from_observations _ g.labels
    (g.first.observed false (by simp) zero) (g.second.observed false (by simp) zero)
    (g.third.observed false (by simp) zero) (g.scalar.forces zero)
    g.oddFirst g.lastNonzero g.anchorNonzero g.anchor g.abscissas).2.2

/-- It suffices to identify the indices and heights on one ordinary witness
over each nonzero input on the half-line that belongs to the projection. -/
theorem defining_of_selected_witnesses (mark : Bool)
    (integerFibres : ∀ n : Nat, Image false (n:Rat))
    (selection : ∀ T : Rat, 0≤2*T+1 → T≠0 → Image false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ output80 false y=0 ∧ Nonempty (ArithmeticData (decoded y))) :
    ∀ T, Image mark T ↔ InputRestriction.IsInteger T := by
  apply (defining_iff_half mark).mpr
  refine ⟨integerFibres,?_⟩
  intro T half belongs
  by_cases zero : T=0
  · exact ⟨0,zero⟩
  obtain ⟨y,input,vanishes,arithmetic⟩:=selection T half zero belongs
  rw [←input]
  exact integer_of_arithmetic80 false y vanishes (fun _=>arithmetic)

#print axioms ordinary_decoded
#print axioms ScalarGeometry.forces
#print axioms integer_of_arithmetic80
#print axioms defining_of_selected_witnesses
end ProjectionFibres.Actual
