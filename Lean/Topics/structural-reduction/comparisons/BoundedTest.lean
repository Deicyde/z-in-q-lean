import SingleContact

namespace StructuralReduction
open Lean.Grind Std
open ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K]

/-- Integer normalization. The value on zero is never used. -/
structure Place (K : Type) [Field K] where
  v : K → Int
  one : v 1 = 0
  mul : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → v (x*y) = v x + v y
  add : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x+y ≠ 0 → min (v x) (v y) ≤ v (x+y)
  unequal : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → v x ≠ v y →
    x+y ≠ 0 ∧ v (x+y) = min (v x) (v y)

def scaled (c y : K) := c*(y*y)
def bounded (c y : K) := scaled c y / (1+scaled c y)
def deep (v : Place K) (k : Int) (y : K) := y=0 ∨ k ≤ v.v y

private theorem nonzero_product {x y : K} (h : x≠0) (k : y≠0) : x*y≠0 :=
  fun e => (Field.of_mul_eq_zero e).elim h k

private theorem numerator (v : Place K) {c y : K} (hc : c≠0) (hy : y≠0) :
    scaled c y ≠ 0 ∧ v.v (scaled c y)=v.v c+2*v.v y := by
  have h := nonzero_product hy hy
  exact ⟨nonzero_product hc h, by unfold scaled; rw [v.mul hc h,v.mul hy hy]; omega⟩

private theorem quotient (v : Place K) {c y : K} (hc : c≠0) (hy : y≠0)
    (hden : 1+scaled c y ≠ 0) :
    bounded c y ≠ 0 ∧ v.v (bounded c y)=v.v c+2*v.v y-v.v (1+scaled c y) := by
  obtain ⟨hn,hv⟩ := numerator v hc hy
  have e : bounded c y * (1+scaled c y)=scaled c y := Field.div_mul_cancel hden
  have hz : bounded c y ≠ 0 := by
    intro z
    rw [z,Semiring.zero_mul] at e
    exact hn e.symm
  have ord := congrArg v.v e
  rw [v.mul hz hden,hv] at ord
  exact ⟨hz,by omega⟩

theorem unit_depth (v : Place K) {c y : K} (hc : c≠0) (unit : v.v c=0)
    (hden : 1+scaled c y≠0) {m : Int} (hm : 1≤m) :
    deep v (2*m-1) (bounded c y) ↔ deep v m y := by
  by_cases hy : y=0
  · subst y
    simp [deep,bounded,scaled,Semiring.mul_zero,Semiring.add_zero,Field.div_eq_mul_inv,Semiring.zero_mul]
  · obtain ⟨hn,hv⟩ := numerator v hc hy
    obtain ⟨hz,hq⟩ := quotient v hc hy hden
    have ho : (1:K)≠0 := (Ne.symm Field.zero_ne_one)
    simp only [deep,hy,hz,false_or]
    by_cases z : v.v y=0
    · have hal := v.add ho hn hden
      rw [v.one,hv,unit,z] at hal
      omega
    · have hd : v.v 1 ≠ v.v (scaled c y) := by rw [v.one,hv,unit]; omega
      have eq := (v.unequal ho hn hd).2
      rw [v.one,hv,unit] at eq
      omega

theorem preparing_integral (v : Place K) {c y : K} (hc : c≠0) (odd : OddOrder (v.v c)) :
    1+scaled c y≠0 ∧ deep v 0 (bounded c y) := by
  by_cases hy : y=0
  · subst y
    have ho : (1:K) ≠ 0 := Ne.symm Field.zero_ne_one
    simp [deep,bounded,scaled,Semiring.mul_zero,Semiring.add_zero,Field.div_eq_mul_inv,
          Semiring.zero_mul,ho]
  · obtain ⟨hn,hv⟩ := numerator v hc hy
    obtain ⟨n,hn'⟩ := odd
    have hd : v.v 1 ≠ v.v (scaled c y) := by rw [v.one,hv,hn']; omega
    obtain ⟨nz,eq⟩ := v.unequal (Ne.symm Field.zero_ne_one) hn hd
    rw [v.one,hv] at eq
    have hq := (quotient v hc hy nz).2
    exact ⟨nz,Or.inr (by omega)⟩

noncomputable def extended (v : Place K) (x : K) : Option Int := by
  classical
  exact if x=0 then none else some (v.v x)

private theorem extended_depth (v : Place K) (x : K) (k : Int) :
    DepthAtLeast k (extended v x) ↔ deep v k x := by
  classical
  by_cases h : x=0 <;> simp [extended,h,DepthAtLeast,deep]

/-- All raw tests attain their original orders at the same place.
d(v) is the order of the displacement t−1. -/
theorem common_place {P I : Type} (ps : List P) (val : P→Place K) (w d : P→Int)
    (Y : I→K) (m : I→Int) {c : K} (hc : c≠0)
    (unit : ∀ v∈ps,(val v).v c=0) (delta : ∀ v∈ps,0≤d v)
    (regular : ∀ i,1+scaled c (Y i)≠0) (pos : ∀ i,1≤m i)
    {a wm tr b : Int} (maximum : (ps.map w).max?=some wm) (nonpos : ∀ v∈ps,w v≤0)
    (odd : OddOrder a) (trace : -wm≤tr) (pole : b=a-2*tr) (integral : 0≤b)
    (factor : ∀ v∈ps, ∀ i z, extended (val v) (bounded c (Y i))=some z →
       w v ≤ min 0 ((1-2*(2*m i-1))*a+2*(z-2*m i*d v))) :
    0<a ∧ ∃ v∈ps, w v=wm ∧ ∀ i,deep (val v) (m i) (Y i) := by
  classical
  have hfactor : ∀ v∈ps, ∀ i z, extended (val v) (bounded c (Y i))=some z →
       w v ≤ min 0 ((1-2*(2*m i-1))*a+2*z) := by
    intro v hv i z h
    have ht := factor v hv i z h
    have hd := Int.mul_nonneg (show 0≤2*m i by have := pos i; omega) (delta v hv)
    omega
  obtain ⟨ha,v,hv,hw,hi⟩ := one_place ps w (fun v i => extended (val v) (bounded c (Y i)))
    (fun i => 2*m i-1) maximum nonpos odd trace pole integral (fun i => by change 1≤2*m i-1; have := pos i; omega) hfactor
  exact ⟨ha,v,hv,hw,fun i => (unit_depth (val v) hc (unit v hv) (regular i) (pos i)).mp
      ((extended_depth ..).mp (hi i))⟩

theorem preparing_exponents {a nu k : Int} (lo : 1≤k) (hi : k≤79)
    (plus : 8+261*a≤nu) (minus : 8-261*a≤nu) :
    a-nu≤ -2 ∧ 2≤3*nu+(10*k-8)*a ∧ 5≤nu-6*a := by
  by_cases ha : 0≤a
  · have h := Int.mul_nonneg (show 0≤10*k-8 by omega) ha
    omega
  · have h := Int.mul_nonneg (show 0≤782-(10*k-8) by omega) (show 0≤ -a by omega)
    rw [Int.mul_neg,Int.sub_mul] at h
    omega

#print axioms unit_depth
#print axioms preparing_integral
#print axioms common_place
#print axioms preparing_exponents
end StructuralReduction
