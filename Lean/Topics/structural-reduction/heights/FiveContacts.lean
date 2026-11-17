import Std

namespace StructuralHeights

/-- Positive primality in the divisor formulation, over core Lean. -/
def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

private theorem prime_coprime {p : Nat} (hp : Prime p) {a : Int} (ha : ¬(p:Int) ∣ a) :
    p.Coprime a.natAbs := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a.natAbs) with h|h
  · exact h
  · exact False.elim (ha (Int.ofNat_dvd_left.mpr (h ▸ Nat.gcd_dvd_right p a.natAbs)))

theorem prime_dvd_mul {p : Nat} (hp : Prime p) {a b : Int} :
    (p:Int) ∣ a*b ↔ (p:Int) ∣ a ∨ (p:Int) ∣ b := by
  constructor
  · intro h
    by_cases ha : (p:Int) ∣ a
    · exact Or.inl ha
    · apply Or.inr
      apply Int.ofNat_dvd_left.mpr
      apply (prime_coprime hp ha).dvd_of_dvd_mul_left
      simpa only [← Int.natAbs_mul] using Int.ofNat_dvd_left.mp h
  · rintro (a|b)
    · exact Int.dvd_mul_of_dvd_left a
    · exact Int.dvd_mul_of_dvd_right b

private theorem not_div_one {p : Nat} (hp : Prime p) : ¬(p:Int) ∣ 1 := by
  intro h
  have := Nat.le_of_dvd (by decide : 0<1) (Int.ofNat_dvd_left.mp h)
  have := hp.1
  omega

theorem prime_dvd_base {p : Nat} (hp : Prime p) {a : Int} (k : Nat) (h : (p:Int) ∣ a^k) :
    (p:Int) ∣ a := by
  induction k with
  | zero => exact False.elim (not_div_one hp (by simpa using h))
  | succ k ih =>
    rw [Int.pow_succ] at h
    exact ((prime_dvd_mul hp).mp h).elim ih id

/-- An exact order is witnessed by an integer unit after removing the stated prime power. -/
def Exact (p k : Nat) (a : Int) : Prop := ∃ u : Int, a = (p:Int)^k*u ∧ ¬(p:Int) ∣ u

def OddOrder (p : Nat) (a : Int) : Prop := ∃ k, Exact p (2*k+1) a

private theorem exact_unit {p : Nat} {a : Int} (unit : ¬(p:Int) ∣ a) : Exact p 0 a :=
  ⟨a,by simp,unit⟩

private theorem exact_mul {p i j : Nat} (hp : Prime p) {a b : Int}
    (ha : Exact p i a) (hb : Exact p j b) : Exact p (i+j) (a*b) := by
  obtain ⟨u,rfl,hu⟩ := ha
  obtain ⟨v,rfl,hv⟩ := hb
  exact ⟨u*v,by rw [Int.pow_add]; grobner,fun h=>((prime_dvd_mul hp).mp h).elim hu hv⟩

private theorem exact_unique {p : Nat} (hp : Prime p) {a : Int} {i j : Nat}
    (hi : Exact p i a) (hj : Exact p j a) : i=j := by
  obtain ⟨u,eu,hu⟩ := hi
  obtain ⟨v,ev,hv⟩ := hj
  have nz : (p:Int) ≠ 0 := by have := hp.1; omega
  have no_lt {m n : Nat} {s t : Int} (unit : ¬(p:Int) ∣ s)
      (e : (p:Int)^m*s=(p:Int)^n*t) : ¬m<n := by
    intro lt
    have ex : n=m+((n-m-1)+1) := by omega
    rw [ex,Int.pow_add,Int.mul_assoc] at e
    have cancel := Int.eq_of_mul_eq_mul_left (Int.pow_ne_zero nz) e
    apply unit
    rw [cancel,Int.pow_succ,Int.mul_comm ((p:Int)^(n-m-1)) _,Int.mul_assoc]
    exact Int.dvd_mul_right _ _
  have lo := no_lt hu (eu.symm.trans ev)
  have hi := no_lt hv (ev.symm.trans eu)
  omega

private theorem exists_exact (p : Nat) (hp : Prime p) (a : Int) (ha : a≠0) :
    ∃ k, Exact p k a := by
  by_cases h : (p:Int) ∣ a
  · obtain ⟨b,hb⟩ := h
    have nonzero : b≠0 := by intro z; simp [z] at hb; exact ha hb
    have smaller : b.natAbs<a.natAbs := by
      rw [hb,Int.natAbs_mul,Int.natAbs_natCast]
      exact (Nat.lt_mul_iff_one_lt_left (Int.natAbs_pos.mpr nonzero)).mpr hp.1
    obtain ⟨k,u,eq,unit⟩ := exists_exact p hp b nonzero
    exact ⟨k+1,u,by rw [hb,eq,Int.pow_succ];grobner,unit⟩
  · exact ⟨0,exact_unit h⟩
termination_by a.natAbs

private theorem odd_zero {p : Nat} (hp : Prime p) : ¬OddOrder p 0 := by
  rintro ⟨k,u,e,hu⟩
  have nz : (p:Int)≠0 := by have := hp.1; omega
  have zu := (Int.mul_eq_zero.mp e.symm).resolve_left (Int.pow_ne_zero nz)
  exact hu (zu ▸ Int.dvd_zero _)

theorem odd_dvd {p : Nat} {a : Int} (h : OddOrder p a) : (p:Int) ∣ a := by
  obtain ⟨k,u,eq,_⟩ := h
  rw [eq,Int.pow_succ,Int.mul_comm ((p:Int)^(2*k)) _,Int.mul_assoc]
  exact Int.dvd_mul_right _ _

theorem odd_times_unit {p : Nat} (hp : Prime p) {a u : Int} (hu : ¬(p:Int) ∣ u) :
    OddOrder p (a*u) ↔ OddOrder p a := by
  by_cases zero : a=0
  · simp [zero]
  obtain ⟨i,hi⟩ := exists_exact p hp a zero
  have hh : Exact p i (a*u) := by simpa using exact_mul hp hi (exact_unit hu)
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,exact_unique hp hk hh ▸ hi⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,by simpa using exact_mul hp hk (exact_unit hu)⟩

theorem odd_times_square {p : Nat} (hp : Prime p) {a z : Int} (nz : z≠0) :
    OddOrder p (a*z^2) ↔ OddOrder p a := by
  by_cases zero : a=0
  · simp [zero]
  obtain ⟨i,hi⟩ := exists_exact p hp a zero
  obtain ⟨j,hj⟩ := exists_exact p hp z nz
  have hh : Exact p (i+(j+j)) (a*z^2) := by simpa [Int.pow_succ] using exact_mul hp hi (exact_mul hp hj hj)
  constructor
  · rintro ⟨k,hk⟩
    have e := exact_unique hp hk hh
    have ex : i=2*(k-j)+1 := by omega
    exact ⟨k-j,ex ▸ hi⟩
  · rintro ⟨k,hk⟩
    have e := exact_unique hp hk hi
    have ex : i+(j+j)=2*(k+j)+1 := by omega
    exact ⟨k+j,ex ▸ hh⟩

private def product : List Int → Int
  | [] => 1
  | a::l => a*product l

private theorem prod_unit {p : Nat} (hp : Prime p) (l : List Int)
    (units : ∀ x ∈ l, ¬(p:Int)∣x) : ¬(p:Int)∣product l := by
  induction l with
  | nil => exact not_div_one hp
  | cons a l ih =>
    intro h
    exact ((prime_dvd_mul hp).mp h).elim (units a (by simp))
      (ih fun x hx=>units x (List.mem_cons_of_mem _ hx))

private theorem odd_product {p : Nat} (hp : Prime p) (l : List Int)
    (separate : l.Pairwise (fun a b => (p:Int)∣a → ¬(p:Int)∣b)) :
    OddOrder p (product l) ↔ ∃ x ∈ l, OddOrder p x := by
  induction l with
  | nil => simp only [product,List.not_mem_nil,false_and,exists_false,iff_false]
           exact fun h=>not_div_one hp (odd_dvd h)
  | cons a l ih =>
    obtain ⟨head,tail⟩:=List.pairwise_cons.mp separate
    by_cases h : (p:Int)∣a
    · have units : ∀x∈l, ¬(p:Int)∣x := fun x hx=>head x hx h
      rw [product,odd_times_unit hp (prod_unit hp l units)]
      constructor
      · exact fun ha=>⟨a,by simp,ha⟩
      · rintro ⟨x,hx,ox⟩
        rcases List.mem_cons.mp hx with eq|rest
        · simpa only [eq] using ox
        · exact False.elim (units x rest (odd_dvd ox))
    · rw [product,Int.mul_comm,odd_times_unit hp h,ih tail]
      constructor
      · rintro ⟨x,hx,ox⟩; exact ⟨x,List.mem_cons_of_mem _ hx,ox⟩
      · rintro ⟨x,hx,ox⟩
        rcases List.mem_cons.mp hx with rfl|rest
        · exact False.elim (h (odd_dvd ox))
        · exact ⟨x,rest,ox⟩

abbrev Pair := Int × Int

def det (x b : Pair) : Int := x.1*b.2 - x.2*b.1
def marks : List Pair := [(-1,0),(0,1),(1,1),(2401,1),(-343,32)]

/-- Both coordinates are integral and coprime. -/
def Primitive (x : Pair) := Int.gcd x.1 x.2 = 1

def Contact (p : Nat) (x : Pair) : Prop := ∃ m ∈ marks, OddOrder p (det x m)

def quintic (a b : Int) := b*a*(a-b)*(a-2401*b)*(32*a+343*b)

private theorem primitive_not_both {p : Nat} (hp : Prime p) {x : Pair} (prim : Primitive x)
    (first : (p:Int)∣x.1) : ¬(p:Int)∣x.2 :=
  fun second => not_div_one hp ((Int.gcd_eq_one_iff.mp prim) _ first second)

private theorem disjoint {p : Nat} (hp : Prime p) {x m n : Pair} (prim : Primitive x)
    (good : ¬(p:Int)∣det m n) (h : (p:Int)∣det x m) : ¬(p:Int)∣det x n := by
  intro h'
  have first : (p:Int)∣x.1*det m n := by
    have e : x.1*det m n = m.1*det x n - n.1*det x m := by unfold det;grobner
    rw [e];exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h') (Int.dvd_mul_of_dvd_right h)
  have second : (p:Int)∣x.2*det m n := by
    have e : x.2*det m n = m.2*det x n - n.2*det x m := by unfold det;grobner
    rw [e];exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h') (Int.dvd_mul_of_dvd_right h)
  exact primitive_not_both hp prim (((prime_dvd_mul hp).mp first).resolve_right good)
    (((prime_dvd_mul hp).mp second).resolve_right good)

theorem chart_separation : marks.Pairwise (fun m n => det m n ∣ (210:Int)^5) := by decide

/-- Exact parity of the five primitive contact determinants, including infinity. -/
theorem contact_iff_quintic {p : Nat} (hp : Prime p) (good : ¬(p:Int)∣210)
    (x : Pair) (prim : Primitive x) : Contact p x ↔ OddOrder p (quintic x.1 x.2) := by
  let values := marks.map (det x)
  have sep : values.Pairwise (fun a b => (p:Int)∣a → ¬(p:Int)∣b) := by
    apply List.pairwise_map.mpr
    exact chart_separation.imp fun h=>disjoint hp prim (fun bad=>good (prime_dvd_base hp 5 (Int.dvd_trans bad h)))
  have eq : product values = quintic x.1 x.2 := by
    simp only [values,marks,List.map_cons,List.map_nil,product,det,quintic]
    grobner
  rw [←eq,odd_product hp values sep]
  constructor
  · rintro ⟨m,hm,ho⟩
    exact ⟨det x m,List.mem_map.mpr ⟨m,hm,rfl⟩,ho⟩
  · rintro ⟨a,ha,ho⟩
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha
    exact ⟨m,hm,ho⟩

#print axioms chart_separation
#print axioms contact_iff_quintic
end StructuralHeights
