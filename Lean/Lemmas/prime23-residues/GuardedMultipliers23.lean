import AllMultipliers23

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} [NeZero p]

/-- The binary law is used only on an affine nonzero reciprocal with two
vanishing residue coordinates. No equality is required outside this chart. -/
def GuardedValues (p : Nat) [NeZero p] (D : Q2) (q : Int→Q2) (a b : Int→List Int) : Prop :=
  ∀ i m : Int, i≠0 → m≠0 → q i≠(0,0) → PairRed p (q i) (0,0) →
    DivisionValue D (q i) (q (i*m)) m (a m) (b m)

theorem Normalized.nonzero (hp : 1<p) {q y : Q2} {m : Rat}
    (h : Normalized p q y m) (qn : q≠(0,0)) (mn : m≠0) : y≠(0,0) := by
  obtain ⟨u,ur,ue⟩:=h
  have nn : norm q≠0 := by
    intro eq
    obtain ⟨a,b⟩:=(CircuitTransport.Quadratic.norm_zero_iff q.1 q.2).mp eq
    exact qn (Prod.ext a b)
  have un:=(ur.invOne hp).1
  have normScaled : norm (scale (m^2) q)=(m*m)*(m*m)*norm q := by
    dsimp [scale,norm]; grobner
  have nz : norm y≠0 := by
    rw [ue,norm_product,normScaled]
    grind [Rat.mul_eq_zero]
  exact fun z=>nz (by rw [z]; decide +kernel)

private theorem guarded_iterate (hp : BinaryQuartic.Prime p)
    {D : Q2} (Di : IntegralPair p D) {q : Int→Q2} {a b : Int→List Int}
    (law : GuardedValues p D q a b) (live : q 1≠(0,0))
    (base : ∃t, IntegralPair p t ∧ q 1=scale ((p:Rat)^2) t) (k : Nat) :
    Normalized p (q 1) (q ((p:Int)^k)) ((p:Rat)^k) ∧
    ∃t, IntegralPair p t ∧ q ((p:Int)^k)=scale ((p:Rat)^2) t := by
  induction k with
  | zero => simpa only [Int.pow_zero,Rat.pow_zero] using And.intro (normalized_one (p:=p) (q 1)) base
  | succ k ih =>
    obtain ⟨carry,t,it,depth⟩:=ih
    obtain ⟨zero,h,hr,he⟩:=prime_input depth it
    have pn : (p:Int)≠0 := by have pos:=hp.1; omega
    have pr : (p:Rat)≠0 := fun z=>pn (by have hz:=Rat.natCast_eq_zero_iff.mp z; omega)
    have pow_ne := (power_order (primeOrder p hp) pr k).1
    have hval:=law ((p:Int)^k) (p:Int) (Int.pow_ne_zero pn) pn
      (carry.nonzero hp.1 live pow_ne) zero
    have step : Normalized p (q ((p:Int)^k)) (q ((p:Int)^k*p)) (p:Rat) := by
      exact binary_multiplier hp.1 (p:Int) _ _ zero hr he Di hval
    have longer:=carry.trans step
    obtain ⟨u,ur,ue⟩:=step
    have depth':=preserve_depth (m:=(p:Int)) depth it ur ue
    simpa only [Int.pow_succ,Rat.pow_succ] using And.intro longer depth'

theorem guarded_all (hp : BinaryQuartic.Prime p)
    (unitSquare : ∀r : Fin p, r≠0 → r*r=1) {D : Q2} (Di : IntegralPair p D)
    {q : Int→Q2} {a b : Int→List Int} (law : GuardedValues p D q a b) (live : q 1≠(0,0))
    (base : ∃t, IntegralPair p t ∧ q 1=scale ((p:Rat)^2) t) (n : Int) (hn : n≠0) :
    Normalized p (q 1) (q n) (n:Rat) := by
  obtain ⟨m,factor,unit⟩:=int_split hp.1 n hn
  let k:=intOrder p n
  change n=(p:Int)^k*m at factor
  have mn : m≠0 := fun z=>unit (z ▸ Int.dvd_zero _)
  have pn : (p:Int)≠0 := by have pos:=hp.1; omega
  have pr : (p:Rat)≠0 := fun z=>pn (by have hz:=Rat.natCast_eq_zero_iff.mp z; omega)
  obtain ⟨carry,t,it,depth⟩:=guarded_iterate hp Di law live base k
  have zero := (prime_input depth it).1
  have nonzero : (m:Fin p)≠0 := fun e=>unit
    (Int.dvd_iff_emod_eq_zero.mpr ((IsCharP.intCast_eq_zero_iff p m).mp e))
  obtain ⟨h,hr,he⟩:=unit_input m mn (unitSquare _ nonzero) zero
  have step : Normalized p (q ((p:Int)^k)) (q ((p:Int)^k*m)) (m:Rat) :=
    binary_multiplier hp.1 m _ _ zero hr he Di
      (law ((p:Int)^k) m (Int.pow_ne_zero pn) mn
        (carry.nonzero hp.1 live (power_order (primeOrder p hp) pr k).1) zero)
  have full:=carry.trans step
  rw [factor,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_natCast]
  exact full

theorem dyadic_guarded {q : Int→Q2} {a b : Int→List Int} (law : GuardedValues 2 Base.D q a b)
    (base : q 1=Base.qP) (n : Int) (hn : n≠0) : Normalized 2 Base.qP (q n) (n:Rat) := by
  let t:=scale 2 (scale (1/8) Base.qP)
  have it : IntegralPair 2 t := ⟨_,Base.dyadic.1.scale (redTwo (p:=2))⟩
  have live : q 1≠(0,0) := by rw [base]; decide +kernel
  have depth : q 1=scale ((2:Rat)^2) t := by rw [base]; decide +kernel
  exact base ▸ guarded_all (prime_of_finite (by decide) (by decide) : BinaryQuartic.Prime 2)
    unit_square_2 (baseD_integral 2) law live ⟨t,it,depth⟩ n hn

theorem triadic_guarded {q : Int→Q2} {a b : Int→List Int} (law : GuardedValues 3 Base.D q a b)
    (base : q 1=Base.qDouble) (n : Int) (hn : n≠0) : Normalized 3 Base.qDouble (q n) (n:Rat) := by
  let t:=scale (1/9) Base.qDouble
  have it : IntegralPair 3 t := ⟨_,Base.triadic.2.1⟩
  have live : q 1≠(0,0) := by rw [base]; decide +kernel
  have depth : q 1=scale ((3:Rat)^2) t := by rw [base]; decide +kernel
  exact base ▸ guarded_all (prime_of_finite (by decide) (by decide) : BinaryQuartic.Prime 3)
    unit_square_3 (baseD_integral 3) law live ⟨t,it,depth⟩ n hn

#print axioms dyadic_guarded
#print axioms triadic_guarded
end Prime23
