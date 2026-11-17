import ScalarOrder
import IntegralJet
import GroupPoints

namespace StructuralReduction
open Lean.Grind WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

/-- A normalized discrete valuation on a characteristic-zero field extending the
concrete rational order. The value at zero is immaterial. -/
structure ExtensionPlace (p : Nat) (K : Type) [Field K] where
  incl : RingMap Rat K
  val : K → Int
  agrees : ∀ x : Rat, x≠0 → incl.map x≠0 ∧ val (incl.map x)=order p x
  neg : ∀ a : K, a≠0 → val (-a)=val a
  mul : ∀ a b : K, a≠0 → b≠0 → val (a*b)=val a+val b
  addUnequal : ∀ a b : K, a≠0 → b≠0 → val a≠val b →
    a+b≠0 ∧ val (a+b)=min (val a) (val b)

def rationalPlace {p : Nat} (hp : Prime p) : ExtensionPlace p Rat where
  incl := ⟨id,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl⟩
  val := order p
  agrees := fun _ h=>⟨h,rfl⟩
  neg := (primeOrder p hp).neg
  mul := (primeOrder p hp).mul
  addUnequal := (primeOrder p hp).addUnequal

variable {p : Nat} {K : Type} [Field K]
variable (w : ExtensionPlace p K)

/-- x=0 belongs to every depth layer. -/
def ExtensionPlace.deep (d : Int) (x : K) : Prop := x≠0 → d≤w.val x

theorem ExtensionPlace.deep_add {d : Int} {a b : K} (ha : w.deep d a) (hb : w.deep d b) :
    w.deep d (a+b) := by
  intro nz
  by_cases az : a=0
  · subst a;rw [AddCommMonoid.zero_add] at nz ⊢;exact hb nz
  by_cases bz : b=0
  · subst b;rw [AddCommMonoid.add_zero] at nz ⊢;exact ha nz
  have va:=ha az
  have vb:=hb bz
  by_cases ne : w.val a≠w.val b
  · rw [(w.addUnequal a b az bz ne).2];omega
  · apply Int.le_of_not_gt
    intro lt
    have n : -a≠0 := by intro e;apply az;grobner
    have h:=w.addUnequal (a+b) (-a) nz n (by rw [w.neg a az];omega)
    rw [show a+b+(-a)=b by grobner,w.neg a az,Int.min_eq_left (by omega)] at h
    omega

theorem ExtensionPlace.on_int {n : Int} (hn : n≠0) :
    (n:K)≠0 ∧ w.val (n:K)=order p (n:Rat) := by
  have h:=w.agrees (n:Rat) (fun z=>hn (Rat.intCast_eq_zero_iff.mp z))
  rwa [w.incl.int] at h

theorem ExtensionPlace.product {a b : K} (ha : a≠0) (hb : b≠0) :
    a*b≠0 ∧ w.val (a*b)=w.val a+w.val b :=
  ⟨fun h=>(Field.of_mul_eq_zero h).elim ha hb,w.mul a b ha hb⟩

theorem ExtensionPlace.dominates {a b : K} (ha : a≠0)
    (lower : b≠0 → w.val a<w.val b) : a+b≠0 ∧ w.val (a+b)=w.val a := by
  by_cases bz : b=0
  · rw [bz,AddCommMonoid.add_zero];exact ⟨ha,rfl⟩
  have l:=lower bz
  have h:=w.addUnequal a b ha bz (by omega)
  rw [Int.min_eq_left (by omega)] at h
  exact h

/-- This is the first-order evaluation of the integral multiplication series.
Only the scalar p and the signed p-units are required at points of depth at least two. -/
structure MultiplicationChart (p : Nat) {K : Type} [Field K] (w : ExtensionPlace p K)
    (G : Type) [IntModule G] where
  formal : G → Prop
  z : G → K
  origin : z 0=0
  tangent : ∀ (h : Int) (Q : G), (h=(p:Int) ∨ ¬(p:Int)∣h) →
    formal Q → z Q≠0 → 2≤w.val (z Q) →
    formal (h • Q) ∧ ∃ e : K, w.deep 0 e ∧ z (h • Q)=z Q*((h:K)+z Q*e)

variable {G : Type} [IntModule G]
variable {w} (chart : MultiplicationChart p w G)

private theorem multiply_once {a : Int} {Q : G} (allowed : a=(p:Int) ∨ ¬(p:Int)∣a)
    (nonzero : a≠0) (small : order p (a:Rat)≤1)
    (formal : chart.formal Q) (nz : chart.z Q≠0) (deep : 2≤w.val (chart.z Q)) :
    chart.formal (a • Q) ∧ chart.z (a • Q)≠0 ∧
    w.val (chart.z (a • Q))=w.val (chart.z Q)+order p (a:Rat) := by
  obtain ⟨domain,e,integral,eq⟩:=chart.tangent a Q allowed formal nz deep
  obtain ⟨az,av⟩:=w.on_int nonzero
  have dominates : chart.z Q*e≠0 → w.val (a:K)<w.val (chart.z Q*e) := by
    intro ne
    have en : e≠0 := fun z=>ne (by rw [z,Semiring.mul_zero])
    have := integral en
    rw [w.mul _ _ nz en,av];omega
  obtain ⟨factor,ofactor⟩:=w.dominates az dominates
  have h:=w.product nz factor
  rw [ofactor,av] at h
  exact ⟨domain,eq ▸ h⟩

/-- Exact growth for every nonzero signed multiplier, deduced by factoring the integer
and iterating the p-map. There is no formal logarithm in this proof. -/
theorem MultiplicationChart.multiple (hp : Prime p) {a : Int} {Q : G} (ha : a≠0)
    (formal : chart.formal Q) (nz : chart.z Q≠0) (deep : 2≤w.val (chart.z Q)) :
    chart.formal (a • Q) ∧ chart.z (a • Q)≠0 ∧
    w.val (chart.z (a • Q))=w.val (chart.z Q)+order p (a:Rat) := by
  obtain ⟨u,fact,unit⟩:=int_split hp.1 a ha
  have un : u≠0 := fun e=>unit (e ▸ Int.dvd_zero _)
  have ou:=order_int_unit hp unit
  have first:=multiply_once chart (Or.inr unit) un (by omega) formal nz deep
  have pz : (p:Int)≠0 := by have := hp.1;omega
  have op : order p ((p:Int):Rat)=1 := by rw [Rat.intCast_natCast];exact order_prime hp
  have step (k : Nat) : chart.formal (((p:Int)^k) • (u • Q)) ∧
      chart.z (((p:Int)^k) • (u • Q)) ≠ 0 ∧
      w.val (chart.z (((p:Int)^k) • (u • Q)))=w.val (chart.z Q)+(k:Int) := by
    induction k with
    | zero => simpa only [Int.pow_zero,IntModule.one_zsmul,ou,Int.add_zero,Int.natCast_zero] using first
    | succ k ih =>
      obtain ⟨f,nz',v⟩:=ih
      have h:=multiply_once chart (Or.inl rfl) pz (by omega) f nz' (by omega)
      rw [v,op] at h
      rw [Int.pow_succ,Int.mul_comm ((p:Int)^k),IntModule.mul_zsmul,Int.natCast_succ,
        ←Int.add_assoc]
      exact h
  have h:=step (intOrder p a)
  rw [←IntModule.mul_zsmul,←fact] at h
  rwa [order_int hp]

/-- The source points P=2P₀, R=(n−1)P and H=mP₀+T, 2T=0,
satisfy the scalar contact's genuine signed equality. -/
theorem scalar_group_identity (m n : Int) (P₀ T : G) (kill : (2:Int) • T=0) :
    let R:=(n-1) • ((2:Int) • P₀)
    let H:=m • P₀+T
    m • ((2:Int) • R)=(4*(n-1)) • H := by
  dsimp only
  have e:=(source_points m (n-1) 0 P₀ T kill).1
  rw [scalar_comm m 2,e,←IntModule.mul_zsmul]
  congr 1
  grobner

/-- Recover the literal integer divisor from actual source-point equality and measured
reference/double parameters in one place. A zero index and a zero multiplier are both covered. -/
theorem index_divisor (hp : Prime p) (large : 5≤p) {m n : Int} {H R : G}
    (identity : m • ((2:Int) • R)=(4*(n-1)) • H)
    (Hformal : chart.formal H) (Hnz : chart.z H≠0) (Hd : 2≤w.val (chart.z H))
    (Rformal : chart.formal ((2:Int) • R)) (Rnz : chart.z ((2:Int) • R)≠0)
    (gap : w.val (chart.z H)+17≤w.val (chart.z ((2:Int) • R))) :
    ((p^17:Nat):Int)∣n-1 := by
  by_cases sn : n-1=0
  · rw [sn];exact Int.dvd_zero _
  have cs : 4*(n-1)≠0 := by omega
  obtain ⟨_,cn,vc⟩:=chart.multiple hp cs Hformal Hnz Hd
  have mn : m≠0 := by
    intro mz;apply cn
    rw [←identity,mz,IntModule.zero_zsmul,chart.origin]
  obtain ⟨_,_,vm⟩:=chart.multiple hp mn Rformal Rnz (by omega)
  rw [identity] at vm
  have four : order p 4=0 := by
    apply order_nat_unit (n:=4) hp
    intro h;have := Nat.le_of_dvd (by decide : 0<4) h;omega
  have split := (primeOrder p hp).mul 4 ((n-1:Int):Rat) (by decide) (fun z=>sn (Rat.intCast_eq_zero_iff.mp z))
  change order p (4*((n-1:Int):Rat))=order p 4+order p ((n-1:Int):Rat) at split
  rw [Rat.intCast_mul] at vc
  change w.val (chart.z ((4*(n-1)) • H))=w.val (chart.z H)+order p (4*((n-1:Int):Rat)) at vc
  rw [split,four,Int.zero_add] at vc
  have integer := order_int hp m
  apply power_dvd_of_order hp
  omega

end StructuralReduction
