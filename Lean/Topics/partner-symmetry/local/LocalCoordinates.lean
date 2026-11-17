import AdicQuartic

namespace LocalCoordinates
open Lean.Grind AdicQuartic AdicQuartic.Tower
open Fin.NatCast Fin.IntCast

/-- The canonical inverse limit of Z/p^(n+1)Z, with compatibility by divisibility. -/
structure InverseLimit (p : Nat) where
  digits : (n : Nat) → Fin (p^(n+1))
  compat : ∀ n, (p:Int)^(n+1) ∣ ((digits (n+1)).val:Int)-(digits n).val

def representative {p} (x : InverseLimit p) : Tower p := ⟨fun n => (x.digits n).val,x.compat⟩

private theorem represent_mod (q : Nat) [NeZero q] (a : Int) : (q:Int) ∣ ((a:Fin q).val:Int)-a :=
  (red_eq _ _).mp (red_rep (a:Fin q))

def canonical {p} [NeZero p] (x : Tower p) : InverseLimit p where
  digits n := (x.level n : Fin (p^(n+1)))
  compat n := by
    have upper := represent_mod (p^(n+2)) (x.level (n+1))
    have lower := represent_mod (p^(n+1)) (x.level n)
    rw [Int.natCast_pow, Int.pow_succ _ (n+1)] at upper
    rw [Int.natCast_pow] at lower
    obtain ⟨u,hu⟩ := upper
    obtain ⟨v,hv⟩ := lower
    obtain ⟨w,hw⟩ := x.compat n
    exact ⟨(p:Int)*u-v+w,by grobner⟩

private theorem lim_ext {p} {x y : InverseLimit p} (eq : ∀ n, x.digits n=y.digits n) : x=y := by
  cases x with
  | mk f hf =>
    cases y with
    | mk g hg =>
      have e : f=g := funext eq
      subst g
      rfl

theorem canonical_representative {p} [NeZero p] (x : InverseLimit p) :
    canonical (representative x) = x := by
  apply lim_ext; intro n
  exact red_rep (x.digits n)

theorem canonical_eq_iff {p} [NeZero p] (x y : Tower p) : canonical x=canonical y ↔ x.Equal y := by
  constructor
  · intro h n
    have e := congrArg (fun z : InverseLimit p => z.digits n) h
    change (x.level n:Fin (p^(n+1))) = (y.level n:Fin (p^(n+1))) at e
    have v := (red_eq _ _).mp e
    simpa only [Int.natCast_pow] using v
  · intro h
    apply lim_ext; intro n
    apply (red_eq _ _).mpr
    simpa only [Int.natCast_pow] using h n

/-- All later representatives agree at an earlier level. -/
theorem compatible_later {p} (x : Tower p) (n k : Nat) :
    (p:Int)^(n+1) ∣ x.level (n+k)-x.level n := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨u,hu⟩ := ih
    obtain ⟨v,hv⟩ := x.compat (n+k)
    rw [show n+k+1=n+1+k by omega,Int.pow_add] at hv
    refine ⟨u+(p:Int)^k*v,?_⟩
    grobner

private theorem first_true (P : Nat → Prop) (ex : ∃ n, P n) :
    ∃ i, P i ∧ ∀ j, j<i → ¬P j := by
  obtain ⟨n,hn⟩ := ex
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases prior : ∃ i, i<n ∧ P i
    · obtain ⟨i,lt,hi⟩ := prior
      exact ih i lt hi
    · exact ⟨n,hn,fun j hj ph => prior ⟨j,hj,ph⟩⟩

/-- Existence of the order and unit for every nonzero p-adic integer.
    The unit uses the representatives at the shifted levels n+j divided by p^j. -/
theorem unit_factorization {p} [NeZero p] (x : Tower p) (nz : ¬x.Vanishes) :
    ∃ j : Nat, ∃ u : Tower p, u.res≠0 ∧ x.Equal (times (con p ((p:Int)^j)) u) := by
  classical
  have ex : ∃ i, ¬ (p:Int)^(i+1) ∣ x.level i := by
    by_cases q : ∃ i, ¬ (p:Int)^(i+1) ∣ x.level i
    · exact q
    · exact False.elim (nz (fun i => Classical.byContradiction (fun h => q ⟨i,h⟩)))
  obtain ⟨j,bad,prior⟩ := first_true _ ex
  have base : (p:Int)^j ∣ x.level j := by
    cases j with
    | zero => simp
    | succ j =>
      have prev := Classical.not_not.mp (prior j (by omega))
      obtain ⟨u,hu⟩ := prev
      obtain ⟨w,hw⟩ := x.compat j
      exact ⟨u+w,by grobner⟩
  have divides : ∀ n, (p:Int)^j ∣ x.level (j+n) := by
    intro n
    obtain ⟨a,ha⟩ := base
    obtain ⟨b,hb⟩ := compatible_later x j n
    rw [Int.pow_succ] at hb
    exact ⟨a+(p:Int)*b,by grobner⟩
  let terms := fun n : Nat => x.level (j+n)/(p:Int)^j
  have scaled : ∀ n, (p:Int)^j*terms n=x.level (j+n) := by
    intro n
    rw [Int.mul_comm]; exact Int.ediv_mul_cancel (divides n)
  have pow_ne : (p:Int)^j≠0 :=
    Int.pow_ne_zero (by have := NeZero.ne p; omega)
  let u : Tower p := ⟨terms,by
    intro n
    obtain ⟨w,hw⟩ := x.compat (j+n)
    have scale1 := scaled (n+1)
    have scale0 := scaled n
    rw [show j+n+1=j+(n+1) by omega,Int.pow_add] at hw
    refine ⟨w,Int.eq_of_mul_eq_mul_left pow_ne ?_⟩
    grobner⟩
  refine ⟨j,u,?_,?_⟩
  · intro zero
    obtain ⟨w,hw⟩ := (red_zero (terms 0)).mp zero
    apply bad
    have h := scaled 0
    simp only [Nat.add_zero] at h
    rw [Int.pow_succ]
    exact ⟨w,by grobner⟩
  · intro n
    obtain ⟨w,hw⟩ := compatible_later x n j
    have h := scaled n
    rw [Nat.add_comm j n] at h
    exact ⟨-w,by change x.level n-(p:Int)^j*terms n= _; grobner⟩

/-- A numerator with any signed denominator exponent admits a unit-normalized representative. -/
theorem normalize_fraction {p} [NeZero p] (e : Int) (x : Tower p) :
    x.Vanishes ∨ ∃ f : Int, ∃ u : Tower p, u.res≠0 ∧ Balance e f x u := by
  by_cases hz : x.Vanishes
  · exact Or.inl hz
  obtain ⟨j,u,unit,eq⟩ := unit_factorization x hz
  refine Or.inr ⟨e+j,u,unit,?_⟩
  have left : (e-(e+j)).toNat=0 := by omega
  have right : (e+j-e).toNat=j := by omega
  intro n
  change _ ∣ (p:Int)^(e-(e+j)).toNat*x.level n-(p:Int)^(e+j-e).toNat*u.level n
  simpa only [left,right,Int.pow_zero,Int.one_mul] using eq n

/-- A normalized element of the localization: zero, or a signed power times a unit. -/
inductive Coordinate (p : Nat) [NeZero p]
  | zero
  | unitAt (order : Int) (u : Tower p) (unit : u.res≠0)

private def shifted {p} [NeZero p] (m : Int) : Coordinate p → Tower p
  | .zero => con p 0
  | .unitAt e u _ => times (con p ((p:Int)^(e-m).toNat)) u

def RepresentsAt {p} [NeZero p] (m : Int) (u : Tower p) : Coordinate p → Prop
  | .zero => u.Vanishes
  | .unitAt e x _ => Balance m e u x

private theorem shifted_rep {p} [NeZero p] (m e : Int) (le : m≤e) (u : Tower p) (unit : u.res≠0) :
    RepresentsAt m (shifted m (.unitAt e u unit)) (.unitAt e u unit) := by
  intro n
  change _ ∣ (p:Int)^(m-e).toNat*((p:Int)^(e-m).toNat*u.level n) -
    (p:Int)^(e-m).toNat*u.level n
  rw [show (m-e).toNat=0 by omega]
  simp

private theorem shifted_zero {p} [NeZero p] (m : Int) :
    RepresentsAt m (shifted m (.zero : Coordinate p)) .zero := by
  intro n
  exact Int.dvd_zero _

private theorem shifted_unit {p} [NeZero p] (e : Int) (u : Tower p) (unit : u.res≠0) :
    (shifted e (.unitAt e u unit)).res≠0 := by
  simp only [shifted,res_times,res_con,Int.sub_self,Int.toNat_zero,Int.pow_zero,
    Ring.intCast_one,Semiring.one_mul]
  exact unit

/-- Clearing the smaller of the two orders produces a primitive pair in either chart. -/
theorem primitive_coordinates {p} [NeZero p] (x y : Coordinate p)
    (nonzero : x≠.zero ∨ y≠.zero) :
    ∃ m : Int, ∃ u v : Tower p, RepresentsAt m u x ∧ RepresentsAt m v y ∧
      (u.res≠0 ∨ v.res≠0) := by
  cases x with
  | zero =>
    cases y with
    | zero => exact False.elim (nonzero.elim (fun h => h rfl) (fun h => h rfl))
    | unitAt e u hu =>
      exact ⟨e,_,_,shifted_zero e,shifted_rep e e (by omega) u hu,Or.inr (shifted_unit e u hu)⟩
  | unitAt e u hu =>
    cases y with
    | zero =>
      exact ⟨e,_,_,shifted_rep e e (by omega) u hu,shifted_zero e,Or.inl (shifted_unit e u hu)⟩
    | unitAt f v hv =>
      by_cases h : e≤f
      · exact ⟨e,_,_,shifted_rep e e (by omega) u hu,shifted_rep e f h v hv,Or.inl (shifted_unit e u hu)⟩
      · exact ⟨f,_,_,shifted_rep f e (by omega) u hu,shifted_rep f f (by omega) v hv,Or.inr (shifted_unit f v hv)⟩

/-- The criterion with coefficients supplied as canonical, compatible finite residues. -/
theorem inverse_limit_criterion {p} [NeZero p] (prime : BinaryQuartic.Prime p) (odd : p%2=1)
    (e : Int) (k a b c d : InverseLimit p)
    (hk : (representative k).res≠0) (ha : (representative a).res≠0)
    (hb : (representative b).res≠0) (hc : (representative c).res≠0)
    (hd : (representative d).res≠0)
    (det : (representative a).res*(representative d).res -
      (representative b).res*(representative c).res≠0) :
    Affine e (representative k) (representative a) (representative b)
      (representative c) (representative d) ↔ (∃ h : Int, e=2*h) ∨
      Root (representative a).res (representative b).res (representative c).res (representative d).res :=
  (affine_iff prime odd e _ _ _ _ _ hk ha hb hc hd det).trans
    (soluble_iff prime odd e _ _ _ _ _ hk ha hb hc hd det)

end LocalCoordinates

#print axioms LocalCoordinates.canonical_representative
#print axioms LocalCoordinates.canonical_eq_iff
#print axioms LocalCoordinates.unit_factorization
#print axioms LocalCoordinates.normalize_fraction
#print axioms LocalCoordinates.primitive_coordinates
#print axioms LocalCoordinates.inverse_limit_criterion
