import ComparisonBudget
import PhysicalSlope

namespace ComparisonScale
open ProjectionFibres.Comparison ProjectionFibres.HeightSupport
open StructuralReduction StructuralReduction.Transfer84
open BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind

private theorem product (v : RationalOrder) {a b : Rat} {i j : Int}
    (ha : a≠0 ∧ v.ord a=i) (hb : b≠0 ∧ v.ord b=j) :
    a*b≠0 ∧ v.ord (a*b)=i+j :=
  ⟨by grind [Rat.mul_eq_zero],by rw [v.mul _ _ ha.1 hb.1,ha.2,hb.2]⟩

private theorem linear (v : RationalOrder) {a c t : Rat} (ha : a≠0 ∧ v.ord a=0)
    (hc : c≠0 ∧ v.ord c=0) (ht : t≠0) (h : v.ord t≠0) :
    a*t+c≠0 ∧ v.ord (a*t+c)=min (v.ord t) 0 := by
  have at' := product v ha ⟨ht,rfl⟩
  rw [Int.zero_add] at at'
  have sum := v.addUnequal (a*t) c at'.1 hc.1 (by rw [at'.2,hc.2];exact h)
  rwa [at'.2,hc.2] at sum

private theorem physicalOrder {p : Nat} (hp : Prime p) (constant : ¬p∣1952786)
    {R s t common : Rat} (R0 : R≠0) (t0 : t≠0) (slopeEq : t=s^2*common)
    (physicalEq : R*(1952786*s^10*(t-1)^6)=P t) (odd : OddOrder (order p common)) :
    let h := order p common + 2*order p s
    order p R = (if 0<h then h else -h)-10*order p s := by
  let v:=primeOrder p hp
  have sr : s≠0 := by intro e;apply t0;rw [slopeEq,e];grobner
  have lr : common≠0 := by intro e;apply t0;rw [slopeEq,e];grobner
  have sv := power_order v sr 2
  have tv := v.mul _ _ sv.1 lr
  rw [←slopeEq,sv.2] at tv
  change order p t=2*order p s+order p common at tv
  obtain ⟨k,lk⟩:=odd
  have h : v.ord t≠0 := by change order p t≠0;omega
  have unit (n : Nat) (nn : n≠0) (nd : n∣1952786) :
      (n:Rat)≠0 ∧ v.ord (n:Rat)=0 :=
    ⟨fun nz=>nn (Rat.natCast_eq_zero_iff.mp nz),
     order_nat_unit hp (fun pn=>constant (Nat.dvd_trans pn nd))⟩
  have one : (1:Rat)≠0 ∧ v.ord 1=0 := ⟨by decide,v.one⟩
  have negOne : (-1:Rat)≠0 ∧ v.ord (-1)=0 :=
    ⟨by decide,(v.neg 1 one.1).trans v.one⟩
  have two : (2:Rat)≠0 ∧ v.ord 2=0 := unit 2 (by decide) (by decide)
  have thirtyTwo := power_order v two.1 5
  rw [show (2:Rat)^5=32 by decide,two.2,Int.mul_zero] at thirtyTwo
  have c2399 : (2399:Rat)≠0 ∧ v.ord 2399=0 := unit 2399 (by decide) (by decide)
  have c407 : (407:Rat)≠0 ∧ v.ord 407=0 := unit 407 (by decide) (by decide)
  have c195 : (1952786:Rat)≠0 ∧ v.ord 1952786=0 :=
    unit 1952786 (by decide) (by decide)
  have f2 := linear v two one t0 h
  have f3 := linear v one one t0 h
  rw [Rat.one_mul] at f3
  have f4 := linear v c2399 negOne t0 h
  rw [←Rat.sub_eq_add_neg] at f4
  have f5 := linear v c407 thirtyTwo t0 h
  have fd := linear v one negOne t0 h
  rw [Rat.one_mul,←Rat.sub_eq_add_neg] at fd
  have right := product v (product v (product v (product v ⟨t0,rfl⟩ f2) f3) f4) f5
  change P t ≠ 0 ∧ v.ord (P t) = _ at right
  have s10:=power_order v sr 10
  have d6:=power_order v fd.1 6
  rw [fd.2] at d6
  have left := product v ⟨R0,rfl⟩ (product v (product v c195 s10) d6)
  have eq := left.2.symm.trans ((congrArg v.ord physicalEq).trans right.2)
  change order p R+(0+10*order p s+6*min (order p t) 0)=_ at eq
  change _=order p t+min (order p t) 0+min (order p t) 0+
    min (order p t) 0+min (order p t) 0 at eq
  dsimp only
  split <;> omega

private theorem nonnegativeSum {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K)
    (u : K) (R δ : Rat) (ss : List Step) :
    0≤(ss.map (ComparisonBudget.loss w u R δ)).sum := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
    have node : 0≤ComparisonBudget.loss w u R δ s := by
      classical
      unfold ComparisonBudget.loss
      split <;> omega
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Odd order of the shared slope bounds the order of the scale of each actual frame. -/
theorem scale84 (x : Fin 84→Rat) (marked : Bool) (active : marked=true → cell x 1≠0)
    (zero : output marked x=0) (f : Frame) {p : Nat} (hp : Prime p) (large : 5≤p)
    (away : p≠17) (constant : ¬p∣1952786) {K : Type} [Field K]
    (w : ExtensionPlace p K) {ρ : K} (root : ρ^2=2) (odd : OddOrder (order p (cell x 13))) :
    (0<order p (cell x 13) → 8*order p (scaleRoot x f)<order p (cell x 13)) ∧
    (order p (cell x 13)<0 → 12*order p (scaleRoot x f)< -order p (cell x 13)) := by
  have dom:=fromZero_domain x marked active zero
  obtain ⟨δt,ts,physicalEq⟩:=physical x f dom
  rw [δt] at physicalEq
  have t0 : slope x f≠0 := by
    intro eq
    apply noMark x f dom
    rw [eq];simp [P,Rat.zero_mul]
  have raw:=physicalOrder hp constant (actualDetector x dom f).1 t0 ts physicalEq odd
  dsimp only at raw
  obtain ⟨k,lk⟩:=odd
  have oddR : OddOrder (order p (f.data x).R) := by
    split at raw
    · exact ⟨k-4*order p (scaleRoot x f),by omega⟩
    · exact ⟨-k-1-6*order p (scaleRoot x f),by omega⟩
  obtain ⟨u,_,cap⟩:=ComparisonBudget.budget84 x marked active zero f hp large away w root oddR
  have nonneg:=nonnegativeSum w u (f.data x).R (f.data x).delta (f.data x).steps
  split at raw <;> constructor <;> omega

#print axioms scale84
end ComparisonScale
