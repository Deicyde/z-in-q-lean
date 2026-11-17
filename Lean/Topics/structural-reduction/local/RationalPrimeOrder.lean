import BinaryQuartic
import SingleContact

namespace StructuralReduction
open BinaryQuartic ProgressionWitnesses.SingleContact

/-- Number of successive divisions by p. The value at zero is a sentinel. -/
def natOrder (p n : Nat) : Nat :=
  if h : 1 < p ∧ 0 < n ∧ p ∣ n then natOrder p (n/p) + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self h.2.1 h.1

private theorem unit_not_zero {p u : Nat} (h : ¬p ∣ u) : u ≠ 0 :=
  fun e => h (e ▸ Nat.dvd_zero p)

private theorem nat_unit {p u : Nat} (h : ¬p ∣ u) : natOrder p u = 0 := by
  rw [natOrder, dif_neg (fun e => h e.2.2)]

private theorem nat_split {p : Nat} (hp : 1<p) (n : Nat) (hn : 0<n) :
    ∃ u : Nat, n=p^(natOrder p n)*u ∧ ¬p ∣ u := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hd : p ∣ n
    · have e := Nat.div_mul_cancel hd
      have pos : 0<n/p := Nat.pos_of_ne_zero (fun z => by simp [z] at e;omega)
      obtain ⟨u,hu,nu⟩ := ih (n/p) (Nat.div_lt_self hn hp) pos
      refine ⟨u,?_,nu⟩
      rw [natOrder, dif_pos ⟨hp,hn,hd⟩, Nat.pow_succ]
      calc n = n/p*p := e.symm
           _ = (p^(natOrder p (n/p))*u)*p := congrArg (·*p) hu
           _ = _ := by ac_rfl
    · exact ⟨n,by rw [nat_unit hd];simp,hd⟩

private theorem nat_fact_order {p u : Nat} (hp : 1<p) (h : ¬p ∣ u) (k : Nat) :
    natOrder p (p^k*u) = k := by
  have pu := Nat.pos_of_ne_zero (unit_not_zero h)
  induction k with
  | zero => simpa using nat_unit h
  | succ k ih =>
    have rew : p^(k+1)*u=p*(p^k*u) := by rw [Nat.pow_succ];ac_rfl
    rw [rew,natOrder,dif_pos ⟨hp,Nat.mul_pos (by omega) (Nat.mul_pos (Nat.pow_pos (by omega)) pu),
          Nat.dvd_mul_right p (p^k*u)⟩,Nat.mul_div_cancel_left _ (by omega),ih]

private theorem unit_product {p a b : Nat} (hp : Prime p) (ha : ¬p ∣ a) (hb : ¬p ∣ b) :
    ¬p ∣ a*b := by
  have cop : Nat.Coprime p a := by
    rcases hp.2 _ (Nat.gcd_dvd_left p a) with e|e
    · exact e
    · exact False.elim (ha (e ▸ Nat.gcd_dvd_right p a))
  exact fun h => hb (cop.dvd_of_dvd_mul_left h)

private theorem nat_order_mul {p a b : Nat} (hp : Prime p) (ha : 0<a) (hb : 0<b) :
    natOrder p (a*b)=natOrder p a+natOrder p b := by
  obtain ⟨u,hu,nu⟩:=nat_split hp.1 a ha
  obtain ⟨v,hv,nv⟩:=nat_split hp.1 b hb
  have e : a*b=p^(natOrder p a+natOrder p b)*(u*v) := by
    rw [Nat.pow_add];calc
      a*b=(p^(natOrder p a)*u)*(p^(natOrder p b)*v) := (congrArg (·*b) hu).trans (congrArg ((p^(natOrder p a)*u)*·) hv)
      _=_ := by ac_rfl
  rw [e,nat_fact_order hp.1 (unit_product hp nu nv)]

/-- The exponent of p in the absolute value of a signed integer. -/
def intOrder (p : Nat) (a : Int) : Nat := natOrder p a.natAbs

/-- Additive order on reduced rational numbers, including the sentinel at zero. -/
def order (p : Nat) (x : Rat) : Int := (intOrder p x.num:Int) - natOrder p x.den

theorem int_split {p : Nat} (hp : 1<p) (a : Int) (ha : a ≠ 0) :
    ∃ u : Int, a=(p:Int)^(intOrder p a)*u ∧ ¬(p:Int) ∣ u := by
  obtain ⟨u,eq,nu⟩ := nat_split hp a.natAbs (Int.natAbs_pos.mpr ha)
  have ce : (a.natAbs:Int)=(p:Int)^(intOrder p a)*(u:Int) := by
    simpa only [Int.natCast_mul,Int.natCast_pow,intOrder] using congrArg Int.ofNat eq
  have cu : ¬(p:Int) ∣ (u:Int) := fun d => nu (Int.natCast_dvd_natCast.mp d)
  by_cases pos : 0≤a
  · exact ⟨u,(Int.ofNat_natAbs_of_nonneg pos).symm.trans ce,cu⟩
  · rw [Int.ofNat_natAbs_of_nonpos (by omega)] at ce
    exact ⟨-(u:Int),by rw [Int.mul_neg,←ce,Int.neg_neg],by simpa only [Int.dvd_neg] using cu⟩

private theorem int_fact_order {p : Nat} (hp : 1<p) {u : Int} (hu : ¬(p:Int)∣u) (k : Nat) :
    intOrder p ((p:Int)^k*u)=k := by
  unfold intOrder
  rw [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
  exact nat_fact_order hp (fun d => hu (Int.ofNat_dvd_left.mpr d)) k

private theorem int_order_mul {p : Nat} (hp : Prime p) {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) :
    intOrder p (a*b)=intOrder p a+intOrder p b := by
  unfold intOrder;rw [Int.natAbs_mul]
  exact nat_order_mul hp (Int.natAbs_pos.mpr ha) (Int.natAbs_pos.mpr hb)

private theorem int_add_lt {p : Nat} (hp : 1<p) {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0)
    (lt : intOrder p a < intOrder p b) : a+b ≠ 0 ∧ intOrder p (a+b)=intOrder p a := by
  obtain ⟨u,hu,nu⟩:=int_split hp a ha
  obtain ⟨v,hv,_⟩:=int_split hp b hb
  let k:=intOrder p b-(intOrder p a+1)
  have de : intOrder p b=intOrder p a+(k+1) := by dsimp [k];omega
  let w:=u+(p:Int)*((p:Int)^k*v)
  have unit : ¬(p:Int)∣w := by
    dsimp [w]
    rwa [Int.dvd_add_self_mul]
  have eq : a+b=(p:Int)^(intOrder p a)*w := by
    rw [de,Int.pow_add,Int.pow_succ] at hv
    calc a+b = (p:Int)^(intOrder p a)*u+((p:Int)^(intOrder p a)*((p:Int)^k*(p:Int)))*v :=
               (congrArg (·+b) hu).trans (congrArg ((p:Int)^(intOrder p a)*u+·) hv)
         _ = _ := by dsimp [w];grobner
  refine ⟨?_,eq ▸ int_fact_order hp unit _⟩
  rw [eq]
  have pz : (p:Int)≠0 := by omega
  exact Int.mul_ne_zero (Int.pow_ne_zero pz) (fun e => unit (e ▸ Int.dvd_zero _))

private theorem clear_den (x : Rat) : x*(x.den:Rat)=(x.num:Rat) := by
  have h := Rat.num_divInt_den x
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at h
  exact (congrArg (·*(x.den:Rat)) h.symm).trans (Rat.div_mul_cancel (fun z => x.den_nz (Rat.natCast_eq_zero_iff.mp z)))

private theorem den_ne (x : Rat) : (x.den:Int) ≠ 0 := by have h:=x.den_pos;omega

/-- Any signed integral fraction gives the same order, even before reduction. -/
theorem order_of_fraction {p : Nat} (hp : Prime p) {x : Rat} {a d : Int}
    (ha : a ≠ 0) (hd : d ≠ 0) (eq : x*(d:Rat)=(a:Rat)) :
    x ≠ 0 ∧ order p x=(intOrder p a:Int)-intOrder p d := by
  have hx : x ≠ 0 := fun z => ha (Rat.intCast_eq_zero_iff.mp (by rw [←eq,z,Rat.zero_mul]))
  have cross : x.num*d=a*(x.den:Int) := by
    apply Rat.intCast_inj.mp
    rw [Rat.intCast_mul,Rat.intCast_mul,Rat.intCast_natCast,←clear_den,←eq];grobner
  have rel:=congrArg (intOrder p) cross
  rw [int_order_mul hp (fun z => hx (Rat.num_eq_zero.mp z)) hd,
      int_order_mul hp ha (den_ne x)] at rel
  unfold order
  simp only [intOrder,Int.natAbs_natCast] at rel ⊢
  exact ⟨hx,by omega⟩

private theorem order_mul {p : Nat} (hp : Prime p) {x y : Rat} (hx : x ≠ 0) (hy : y ≠ 0) :
    order p (x*y)=order p x+order p y := by
  have nx : x.num ≠ 0 := fun z => hx (Rat.num_eq_zero.mp z)
  have ny : y.num ≠ 0 := fun z => hy (Rat.num_eq_zero.mp z)
  have rep : (x*y)*(((x.den:Int)*(y.den:Int):Int):Rat)=((x.num*y.num:Int):Rat) := by
    rw [Rat.intCast_mul,Rat.intCast_mul,Rat.intCast_natCast,Rat.intCast_natCast,←clear_den,←clear_den]
    grobner
  have e := (order_of_fraction hp (Int.mul_ne_zero nx ny) (Int.mul_ne_zero (den_ne x) (den_ne y)) rep).2
  rw [int_order_mul hp nx ny,int_order_mul hp (den_ne x) (den_ne y)] at e
  simp only [order,intOrder,Int.natAbs_natCast] at e ⊢
  omega

private theorem order_add_lt {p : Nat} (hp : Prime p) {x y : Rat} (hx : x ≠ 0) (hy : y ≠ 0)
    (lt : order p x<order p y) : x+y ≠ 0 ∧ order p (x+y)=order p x := by
  have nx : x.num ≠ 0 := fun e => hx (Rat.num_eq_zero.mp e)
  have ny : y.num ≠ 0 := fun e => hy (Rat.num_eq_zero.mp e)
  let a:=x.num*(y.den:Int)
  let b:=y.num*(x.den:Int)
  have oa : intOrder p a = intOrder p x.num + natOrder p y.den := int_order_mul hp nx (den_ne y)
  have ob : intOrder p b = intOrder p y.num + natOrder p x.den := int_order_mul hp ny (den_ne x)
  have lower : intOrder p a<intOrder p b := by
    rw [oa,ob];unfold order at lt;omega
  obtain ⟨nz,exactOrd⟩ := int_add_lt hp.1 (Int.mul_ne_zero nx (den_ne y)) (Int.mul_ne_zero ny (den_ne x)) lower
  have rep : (x+y)*(((x.den:Int)*(y.den:Int):Int):Rat)=((a+b:Int):Rat) := by
    dsimp [a,b]
    simp only [Rat.intCast_mul,Rat.intCast_add,Rat.intCast_natCast]
    rw [←clear_den,←clear_den];grobner
  obtain ⟨nn,e⟩ := order_of_fraction hp nz (Int.mul_ne_zero (den_ne x) (den_ne y)) rep
  rw [exactOrd,oa,int_order_mul hp (den_ne x) (den_ne y)] at e
  change _ = _ - (↑(natOrder p x.den+natOrder p y.den):Int) at e
  refine ⟨nn,?_⟩
  change order p (x+y)=(intOrder p x.num:Int)-natOrder p x.den
  omega

/-- The earlier formal pole argument's valuation laws hold for this computable rational order
at every ordinary prime. No value at zero is used by the laws. -/
def primeOrder (p : Nat) (hp : Prime p) : RationalOrder where
  ord := order p
  one := by unfold order intOrder;change (natOrder p 1:Int)-natOrder p 1=0;omega
  neg := by intro x _;simp only [order,intOrder,Rat.neg_num,Rat.neg_den,Int.natAbs_neg]
  mul := fun _ _ => order_mul hp
  div := by
    intro a b ha hb
    have nz : a/b ≠ 0 := fun eq => ha (by rw [←Rat.div_mul_cancel (a:=a) hb,eq,Rat.zero_mul])
    have e:=order_mul hp nz hb
    rw [Rat.div_mul_cancel hb] at e;omega
  addUnequal := by
    intro a b ha hb ne
    by_cases lt : order p a<order p b
    · obtain ⟨z,h⟩:=order_add_lt hp ha hb lt
      exact ⟨z,by rw [h,Int.min_eq_left (by omega)]⟩
    · obtain ⟨z,h⟩:=order_add_lt hp hb ha (by omega)
      rw [Rat.add_comm]
      exact ⟨z,by rw [h,Int.min_eq_right (by omega)]⟩

theorem order_int {p : Nat} (hp : Prime p) (n : Int) : order p (n:Rat)=(intOrder p n:Int) := by
  have nu : ¬p ∣ 1 := fun d => by have := Nat.eq_one_of_dvd_one d;have := hp.1;omega
  simp only [order,Rat.num_intCast,Rat.den_intCast,nat_unit nu,Int.natCast_zero,Int.sub_zero]

theorem order_int_unit {p : Nat} (hp : Prime p) {a : Int} (h : ¬(p:Int)∣a) : order p (a:Rat)=0 := by
  rw [order_int hp];unfold intOrder;rw [nat_unit (fun d=>h (Int.ofNat_dvd_left.mpr d))];rfl

theorem power_dvd_of_order {p : Nat} (hp : Prime p) {a : Int} {k : Nat}
    (h : (k:Int)≤order p (a:Rat)) : ((p^k:Nat):Int) ∣ a := by
  by_cases az : a=0
  · rw [az];exact Int.dvd_zero _
  obtain ⟨u,hu,_⟩:=int_split hp.1 a az
  rw [order_int hp] at h
  have de : intOrder p a=k+(intOrder p a-k) := by omega
  rw [de,Int.pow_add] at hu
  refine ⟨(p:Int)^(intOrder p a-k)*u,?_⟩
  rw [Int.natCast_pow,←Int.mul_assoc];exact hu

theorem order_nat_unit {p n : Nat} (hp : Prime p) (h : ¬p ∣ n) : order p (n:Rat)=0 := by
  rw [←Rat.intCast_natCast,order_int hp]
  change (natOrder p n:Int)=0
  rw [nat_unit h];rfl

theorem order_prime {p : Nat} (hp : Prime p) : order p (p:Rat)=1 := by
  rw [←Rat.intCast_natCast,order_int hp]
  change (natOrder p p:Int)=1
  have hu : ¬p ∣ 1 := fun d => by have := Nat.eq_one_of_dvd_one d;have := hp.1;omega
  have e := nat_fact_order hp.1 hu 1
  simpa only [Nat.pow_one,Nat.mul_one] using congrArg Int.ofNat e

end StructuralReduction
