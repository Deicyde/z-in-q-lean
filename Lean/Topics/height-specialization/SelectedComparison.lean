import Support80
import RationalScaleHeight

namespace HeightSpecialization
open StructuralReduction StructuralReduction.Transfer84 IndependentIndices IndependentIndices.Assembly
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.HeightSupport WitnessTransfer.Height
open ProjectionFibres.Comparison
open BinaryQuartic ProgressionWitnesses.SingleContact
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
abbrev Scale := ProjectionFibres.Comparison.Frame

def maximumFrame (weight : Scale → Nat) : Scale :=
  if weight .first ≥ max (weight .second) (weight .third) then .first
  else if weight .second ≥ weight .third then .second else .third

theorem maximum_value (v : Scale → Nat) :
    v (maximumFrame v)=largest (v .first) (v .second) (v .third) := by
  unfold maximumFrame largest
  split
  · omega
  · split <;> omega

theorem le_maximum (v : Scale → Nat) (f : Scale) : v f≤v (maximumFrame v) := by
  rw [maximum_value v]
  have b:=largest_bounds (v .first) (v .second) (v .third)
  cases f with
  | first => exact b.1
  | second => exact b.2.1
  | third => exact b.2.2

noncomputable def M (x : Fin 84 → Rat) (f : Scale) := radical (fullPrimes (slope x f))

def ComparisonCharts (x : Fin 84→Rat) (f : Scale) (ns : Labels) :=
  ∀ p∈fullPrimes (slope x f), ∃ m, Nonempty (AtContact x f p m ns)

def ScalarCharts (x : Fin 84→Rat) (n : Int) :=
  ∀ p∈scalarFullPrimes (SquareGate.label (cell x 1)), ∃ m, Nonempty (CubicAt p x m n)

theorem selected_defects {x : Fin 84→Rat} {f : Scale} {ns : Labels}
    (zero : output false x=0) (charts : ComparisonCharts x f ns) :
    Defects (M x f) ns (SquareGate.label (cell x 1)) := by
  have domain:=fromZero_domain x false (by simp) zero
  have both {p} (hp : p∈fullPrimes (slope x f)) :
      ((p^40:Nat):Int)∣lucas ns.n₂ ns.n₃ ns.n₄ ∧
      ((p^10:Nat):Int)∣((ns.n₁:Rat)-SquareGate.label (cell x 1)).num := by
    obtain ⟨m,⟨data⟩⟩:=charts p hp
    obtain ⟨observation⟩:=(data.geometry domain hp).observation false (by simp) zero
    obtain ⟨contact⟩:=observation.contact
    exact contact.divides
  exact ⟨aggregate _ _ _ (fun _ hp=>(both hp).1),aggregate _ _ _ (fun _ hp=>(both hp).2)⟩

theorem scalar_contacts {x : Fin 84→Rat} {n : Int} (zero : output false x=0)
    (charts : ScalarCharts x n)
    (height : H (SquareGate.label (cell x 1))≤
      2^(2*scalarConstant*(radical (scalarFullPrimes (SquareGate.label (cell x 1))))^17)) :
    Nonempty (ScalarContacts (cell x 1) n) := by
  let B:=SquareGate.label (cell x 1)
  refine ⟨⟨scalarFullPrimes B,?_,?_,height⟩⟩
  · intro p member
    obtain ⟨prime,good,_,_⟩:=(mem_scalarFullPrimes B p).mp member
    rcases prime.2 _ (Nat.gcd_dvd_right 6 p) with h|h
    · exact h
    · have dvd : p∣6 := h ▸ Nat.gcd_dvd_left 6 p
      exact False.elim (good (Int.natCast_dvd_natCast.mpr (Nat.dvd_trans dvd (by decide : 6∣210))))
  · intro p member
    obtain ⟨hp,good,away,hit⟩:=(mem_scalarFullPrimes B p).mp member
    obtain ⟨m,⟨g⟩⟩:=charts p member
    letI:=g.ground
    letI:=g.group
    letI:=g.group'
    obtain ⟨hr,pos,odd⟩:=physical_contact_order hp good _ hit
    have large : 5≤p := by
      by_cases small : p=2 ∨ p=3
      · rcases small with rfl|rfl <;> exact False.elim (good (by decide))
      · have h4 : p≠4 := by rintro rfl; have h:=hp.2 2 (by decide); omega
        have h:=hp.1;omega
    exact source_scalar_divisor84 false x (by simp) zero g.C g.N hp large away hr pos odd
      g.left g.right g.leftF g.rightF

def SmallInput (t : Rat) := H (SquareGate.label t)^17 ≤ 2^(anchorModulus-5)

def ScalarCondition (x : Fin 84→Rat) (n : Int) :=
  SmallInput (cell x 1) ∨
    (ScalarCharts x n ∧ H (SquareGate.label (cell x 1))≤
      2^(2*scalarConstant*(radical (scalarFullPrimes (SquareGate.label (cell x 1))))^17))

theorem anchor_lower {a : Int} (nonzero : a-1≠0) (anchor : (anchorModulus:Int)∣a-1) :
    anchorModulus-1 ≤ a.natAbs := by
  have lo:=Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) (Int.ofNat_dvd_left.mp anchor)
  have hi:=Int.natAbs_sub_le a 1
  rw [Int.natAbs_one] at hi
  omega

theorem scalar_bound {x : Fin 84→Rat} {a : Int} (z : output false x=0)
    (cond : ScalarCondition x a) (nz : a-1≠0) (anchor : (anchorModulus:Int)∣a-1) :
    H (SquareGate.label (cell x 1))^17 ≤ 2^(a.natAbs-4) := by
  rcases cond with small|⟨charts,height⟩
  · have lo:=anchor_lower nz anchor
    exact Nat.le_trans small (Nat.pow_le_pow_right (by decide) (by omega))
  · obtain ⟨contacts⟩:=scalar_contacts z charts height
    exact scalar_height contacts nz anchor

/-- The end of the height argument consumes precisely the two congruences for one modulus. -/
theorem equal_of_defects {T : Rat} {ns : Labels} {q : Nat}
    (residues : Defects q ns (SquareGate.label T)) (last : ns.n₄≠0)
    (nz : ns.n₂-1≠0) (anchor : (anchorModulus:Int)∣ns.n₂-1)
    (roots : (labelSize ns)^2<rootConstant*q^17)
    (scalar : H (SquareGate.label T)^17≤2^(ns.n₂.natAbs-4)) :
    lucas ns.n₂ ns.n₃ ns.n₄=0 ∧ SquareGate.label T=(ns.n₁:Rat) := by
  have lo:=anchor_lower nz anchor
  have big:=Nat.lt_of_lt_of_le HeightClosure.numerical_bounds.2.2.1 lo
  let L:=labelSize ns
  have sizes : ns.n₁.natAbs≤L ∧ ns.n₂.natAbs≤L ∧ ns.n₃.natAbs≤L ∧ ns.n₄.natAbs≤L := by
    dsimp [L,labelSize];omega
  obtain ⟨h₁,h₂,h₃,h₄⟩:=sizes
  have rootAnchor:=Nat.lt_of_lt_of_le HeightClosure.numerical_bounds.1 (Nat.pow_le_pow_left (Nat.le_trans lo h₂) 12)
  have vanish:=HeightClosure.two_defects roots rootAnchor
    (lucas_magnitude _ _ _ _ (by omega) h₂ h₃ h₄) residues.1 residues.2
    (numerator_magnitude _ _ _ h₁ (by omega)) (by
      intro eq
      have huge:=Nat.le_trans (exponential_size (by omega) last eq) h₃
      have sep : 2^4000≤L := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega)) huge
      exact ⟨Nat.lt_of_lt_of_le HeightClosure.numerical_bounds.2.2.2 (Nat.pow_le_pow_left sep 2),Nat.le_trans scalar huge⟩)
  have e:=Rat.num_eq_zero.mp vanish.2
  exact ⟨vanish.1,by grobner⟩

structure SelectedArithmetic (x : Fin 84→Rat) where
  labels : Labels
  frame : Scale
  charts : ComparisonCharts x frame labels
  roots : (labelSize labels)^2<rootConstant*(M x frame)^17
  scalar : ScalarCondition x labels.n₂
  oddFirst : labels.n₁%2=1
  lastNonzero : labels.n₄≠0
  offsetNonzero : labels.n₂-1≠0
  anchor : (anchorModulus:Int)∣labels.n₂-1

theorem selected_integral {x : Fin 84→Rat} (z : output false x=0) (g : SelectedArithmetic x) :
    InputRestriction.IsInteger (cell x 1) := by
  have eq:=equal_of_defects (selected_defects z g.charts) g.lastNonzero g.offsetNonzero g.anchor
    g.roots (scalar_bound z g.scalar g.offsetNonzero g.anchor)
  exact SquareGate.integer_of_odd_label _ _ g.oddFirst eq.2

theorem circuit_defines_of_one_comparison (marked : Bool)
    (existence : ∀ n : Nat, circuitImage false (n:Rat))
    (choice : ∀ T : Rat, 0≤2*T+1 → T≠0 → circuitImage false T →
      ∃ y : Fin 80→Rat, y 0=T ∧ Binding.V y 9813=0 ∧ Nonempty (SelectedArithmetic (decoded y))) :
    ∀ T, circuitImage marked T ↔ InputRestriction.IsInteger T := by
  apply (circuit_defines_iff marked).mpr
  refine ⟨existence,?_⟩
  intro T half represented
  by_cases zero : T=0
  · exact ⟨0,zero⟩
  obtain ⟨y,hy,eq,⟨g⟩⟩:=choice T half zero represented
  have ordinary:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans eq)
  simpa only [input_decoded,hy] using selected_integral ordinary g

#print axioms maximum_value
#print axioms selected_defects
#print axioms scalar_contacts
#print axioms scalar_bound
#print axioms equal_of_defects
#print axioms selected_integral
#print axioms circuit_defines_of_one_comparison
end HeightSpecialization
