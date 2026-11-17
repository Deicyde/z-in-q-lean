import Scalar84
import ScalarTwists

namespace StructuralReduction.Transfer84
open IndependentIndices Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- Homogenization of the rational scalar read at its actual shared input. -/
theorem scalar_fraction (x : Rat) :
    let z:=SquareGate.value x
    Wires.contact x * (((z.den:Int)^6:Int):Rat) = ((StructuralHeights.sextic z.num z.den:Int):Rat) := by
  let z:=SquareGate.value x
  have g : Wires.gateY x=z := by
    unfold Wires.gateY;dsimp [z,SquareGate.value,SquareGate.shift];grobner
  have dn : (z.den:Rat)≠0 := fun h=>z.den_nz (Rat.natCast_eq_zero_iff.mp h)
  have rep:=Rat.num_divInt_den z
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at rep
  have nz : (z.num:Rat)=z*(z.den:Rat) :=
    (Rat.div_mul_cancel (a:=(z.num:Rat)) dn).symm.trans (congrArg (fun k:Rat=>k*(z.den:Rat)) rep)
  change Wires.contact x * (((z.den:Int)^6:Int):Rat)=((StructuralHeights.sextic z.num z.den:Int):Rat)
  rw [Wires.contact,g]
  unfold Wires.rOfY2 StructuralHeights.sextic StructuralHeights.firstForm
    StructuralHeights.secondForm StructuralHeights.thirdForm
  simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_natCast,nz]
  grobner

private theorem unit_denominator {p : Nat} (hp : StructuralHeights.Prime p) (good : ¬(p:Int)∣210)
    (z : Rat) (div : (p:Int)∣StructuralHeights.sextic z.num z.den) : ¬(p:Int)∣(z.den:Int) := by
  intro denominator
  let u:=z.num
  let v:=(z.den:Int)
  let w:=((77175+32*(2401+2400))*u^4*v+
           (77175*(2401+2400)+32*2401*2400)*u^2*v^3+2401*2400*77175*v^5)
  have eq : StructuralHeights.sextic z.num z.den=32*u^6+v*w := by
    unfold StructuralHeights.sextic StructuralHeights.firstForm StructuralHeights.secondForm StructuralHeights.thirdForm
    dsimp [u,v,w];grobner
  rw [eq] at div
  have piece : (p:Int)∣v*w := Int.dvd_mul_of_dvd_left denominator
  have leading : (p:Int)∣32*u^6 := (Int.dvd_add_left piece).mp div
  have c : ¬(p:Int)∣32 := fun h=>good (StructuralHeights.prime_dvd_base hp 5
                                (Int.dvd_trans h (by decide : (32:Int)∣210^5)))
  have numerator := StructuralHeights.prime_dvd_base hp 6 ((StructuralHeights.prime_dvd_mul hp).mp leading |>.resolve_left c)
  have one := (Int.gcd_eq_one_iff.mp (StructuralHeights.coordinates_primitive z)) _ numerator denominator
  have bound:=Nat.le_of_dvd (by decide : 0<1) (Int.ofNat_dvd_left.mp one)
  have large:=hp.1
  omega

private theorem exact_order {p : Nat} (hp : BinaryQuartic.Prime p) {k : Nat} {a : Int}
    (e : StructuralHeights.Exact p k a) : a≠0 ∧ (intOrder p a:Int)=(k:Int) := by
  obtain ⟨u,eq,unit⟩:=e
  have base : (p:Rat)≠0 := fun h=>by have q:=Rat.natCast_eq_zero_iff.mp h;have :=hp.1;omega
  have uz : u≠0 := fun h=>unit (h ▸ Int.dvd_zero _)
  have ratUnit : (u:Rat)≠0 := fun h=>uz (Rat.intCast_eq_zero_iff.mp h)
  have power:=power_order (primeOrder p hp) base k
  have product:=(primeOrder p hp).mul _ _ power.1 ratUnit
  change order p ((p:Rat)^k*(u:Rat))=order p ((p:Rat)^k)+order p (u:Rat) at product
  have po : order p ((p:Rat)^k)=(k:Int)*order p (p:Rat) := power.2
  refine ⟨fun zero=>?_ ,?_⟩
  · have both : (p:Int)^k*u≠0 := Int.mul_ne_zero (Int.pow_ne_zero (by have := hp.1;omega)) uz
    exact both (eq.symm.trans zero)
  · rw [←order_int hp,eq,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_natCast,product,po,order_prime hp,order_int_unit hp unit]
    omega

/-- A five-mark contact on the physical square gives strictly positive odd order
of the rational scalar itself; its denominator is a unit at that prime. -/
theorem physical_contact_order {p : Nat} (hp : StructuralHeights.Prime p) (good : ¬(p:Int)∣210)
    (x : Rat) (hit : StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label x))) :
    Wires.contact x≠0 ∧ 0<order p (Wires.contact x) ∧
    ProgressionWitnesses.SingleContact.OddOrder (order p (Wires.contact x)) := by
  let z:=SquareGate.value x
  have odd:= (StructuralHeights.physical_contact hp good x).mp hit
  have unit:=unit_denominator hp good z (StructuralHeights.odd_dvd odd)
  obtain ⟨k,exactK⟩:=odd
  have hp' : BinaryQuartic.Prime p := hp
  obtain ⟨nonzero,ord⟩:=exact_order hp' exactK
  have den : (z.den:Int)≠0 := by have := z.den_nz;omega
  obtain ⟨live,frac⟩:=order_of_fraction hp' nonzero (show (z.den:Int)^6≠0 from Int.pow_ne_zero den) (scalar_fraction x)
  have denom := order_int_unit hp' (a:=(z.den:Int)^6) (fun d=>unit (StructuralHeights.prime_dvd_base hp 6 d))
  rw [order_int hp'] at denom
  rw [denom,Int.sub_zero,ord] at frac
  refine ⟨live,by omega,(k:Int),by omega⟩

/-- Rational torsion and rank-zero descent on the three curves exclude their right-hand components. -/
def ThreeCurveExclusion : Prop :=
  ∀ d : Nat, (d=1 ∨ d=2 ∨ d=70) → ∀ X Y Z : Int, 0<Z → 32*(d:Int)*Z^2<X →
    Y^2 ≠ X*(X-32*(d:Int)*Z^2)*(X+343*(d:Int)*Z^2)

private theorem good_size {p : Nat} (hp : StructuralHeights.Prime p) (good : ¬(p:Int)∣210) : 11≤p := by
  have small : ∀ i : Fin 11, 1<i.val → (∀ d : Fin 11, d.val∣i.val → d.val=1 ∨ d.val=i.val) →
      (i.val:Int)∣210 := by decide
  by_cases h : 11≤p
  · exact h
  · exact False.elim (good (small ⟨p,by omega⟩ hp.1 (fun d=>hp.2 d.val)))

theorem good_contact_exists (excluded : ThreeCurveExclusion) (x : Rat) :
    ∃ p, StructuralHeights.Prime p ∧ 11≤p ∧ p≠17 ∧ ¬(p:Int)∣210 ∧
         StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label x)) := by
  apply Classical.byContradiction
  intro empty
  have h : StructuralHeights.EmptyScalar x := by
    intro p hp good hit
    have away : p≠17 := by rintro rfl;exact StructuralHeights.no_contact_17 x hit
    exact empty ⟨p,hp,good_size hp good,away,good,hit⟩
  obtain ⟨d,hd,X,Y,Z,zpos,large,point⟩:=StructuralHeights.empty_elliptic x h
  exact excluded d hd X Y Z zpos large point

/-- The two conjugate group evaluations over one local place, including both
shared reciprocal coordinates in physical slots 21 and 22. -/
def HasScalarCharts (p : Nat) (x : Fin 84→Rat) (m n : Int) (K G G' : Type)
    [Field K] [IntModule G] [IntModule G'] : Prop :=
  ∃ (w : ExtensionPlace p K) (chart : MultiplicationChart p w G) (other : MultiplicationChart p w G')
    (rho : K) (left : ScalarBranch chart m n (cell x 25) (cell x 26) rho)
    (right : ScalarBranch other m n (cell x 25) (cell x 26) (-rho)),
      left.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*rho ∧
      right.shared.f=w.incl.map (cell x 21)+w.incl.map (cell x 22)*(-rho)

/-- Each contact can use its own completion, groups, field and module instances. -/
def HasLocalScalarCharts (p : Nat) (x : Fin 84→Rat) (m n : Int) : Prop :=
  ∃ (K G G' : Type) (fieldK : Field K) (groupG : IntModule G) (groupG' : IntModule G'),
    @HasScalarCharts p x m n K G G' fieldK groupG groupG'

/-- At any good contact of the physical label, read the index divisor from the polynomial zero. -/
theorem scalar_divisor_at_contact84 (marked : Bool) (x : Fin 84→Rat)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0) (m n : Int)
    {p : Nat} (hp : StructuralHeights.Prime p) (good : ¬(p:Int)∣210)
    (hit : StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label (cell x 1))))
    (charts : HasLocalScalarCharts p x m n) : ((p^17:Nat):Int)∣n-1 := by
  have large := good_size hp good
  have away : p≠17 := by
    rintro rfl
    exact StructuralHeights.no_contact_17 _ hit
  obtain ⟨live,pos,odd⟩:=physical_contact_order hp good (cell x 1) hit
  obtain ⟨K,G,G',fieldK,groupG,groupG',both⟩:=charts
  letI : Field K := fieldK
  letI : IntModule G := groupG
  letI : IntModule G' := groupG'
  obtain ⟨w,chart,other,rho,left,right,fplus,fminus⟩:=both
  exact physical_scalar_divisor84 chart other marked x active zero hp (by omega)
    away live pos odd left right fplus fminus

theorem some_scalar_divisor84 (excluded : ThreeCurveExclusion) (marked : Bool) (x : Fin 84→Rat)
    (active : marked=true → cell x 1≠0) (zero : output marked x=0) (m n : Int)
    (charts : ∀ p, StructuralHeights.Prime p → 11≤p → p≠17 →
       StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label (cell x 1))) →
       HasLocalScalarCharts p x m n) :
    ∃ p, StructuralHeights.Prime p ∧ 11≤p ∧ p≠17 ∧
         StructuralHeights.Contact p (StructuralHeights.coordinates (SquareGate.label (cell x 1))) ∧
         ((p^17:Nat):Int)∣n-1 := by
  obtain ⟨p,hp,large,away,good,hit⟩:=good_contact_exists excluded (cell x 1)
  exact ⟨p,hp,large,away,hit,scalar_divisor_at_contact84 marked x active zero m n hp good hit
    (charts p hp large away hit)⟩

#print axioms scalar_fraction
#print axioms physical_contact_order
#print axioms good_contact_exists
#print axioms scalar_divisor_at_contact84
#print axioms some_scalar_divisor84
end StructuralReduction.Transfer84
