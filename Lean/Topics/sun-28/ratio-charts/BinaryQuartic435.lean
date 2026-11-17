import Std
namespace BinaryQuartic
open Lean.Grind

/-- The usual prime-divisor definition. All modular computations below use the ring Fin p. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

private theorem length_bound {α : Type} [DecidableEq α] {l r : List α}
    (nodup : l.Nodup) (inside : ∀ a, a ∈ l → a ∈ r) : l.length ≤ r.length := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
    obtain ⟨away,distinct⟩ := List.nodup_cons.mp nodup
    have ar := inside a (by simp)
    have short := List.length_erase_of_mem ar
    have small : l.length ≤ (r.erase a).length := by
      apply ih distinct
      intro x hx
      have ne : x ≠ a := fun e => away (e ▸ hx)
      exact (List.mem_erase_of_ne ne).mpr (inside x (by simp [hx]))
    simp only [List.length_cons]
    have pos : r.length > 0 := List.length_pos_of_mem ar
    omega

private theorem distinct_image {α : Type} {n : Nat} (f : Fin n → α)
    (inj : ∀ {i j}, f i=f j → i=j) : (List.ofFn f).Nodup := by
  rw [List.Nodup,List.pairwise_iff_getElem]
  intro i j hi hj lt eq
  simp only [List.getElem_ofFn] at eq
  have e := congrArg Fin.val (inj eq)
  change i=j at e
  omega

/-- An injection on all residues hits each residue, proved by finite counting. -/
private theorem onto {p : Nat} (f : Fin p → Fin p) (inj : ∀ {i j}, f i=f j → i=j)
    (a : Fin p) : ∃ x, f x = a := by
  by_cases found : ∃ x, f x=a
  · exact found
  · have ha := List.mem_finRange a
    have card := List.length_erase_of_mem ha
    have le : (List.ofFn f).length ≤ ((List.finRange p).erase a).length := by
      apply length_bound (distinct_image f inj)
      intro x h
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
      have ne : x ≠ a := fun e => found ⟨i,hi.trans e⟩
      exact (List.mem_erase_of_ne ne).mpr (List.mem_finRange x)
    rw [List.length_ofFn] at le
    rw [List.length_finRange] at card
    have := a.isLt
    omega

theorem mul_zero {p : Nat} [NeZero p] (hp : Prime p) {x y : Fin p} (h : x*y=0) :
    x=0 ∨ y=0 := by
  by_cases hx : x=0
  · exact Or.inl hx
  · right
    have rel := congrArg Fin.val h
    rw [Fin.val_mul,Fin.val_zero] at rel
    have gx : Nat.Coprime p x.val := by
      rcases hp.2 _ (Nat.gcd_dvd_left p x.val) with g|g
      · exact g
      · have gd := Nat.gcd_dvd_right p x.val
        rw [g] at gd
        have zero := Nat.eq_zero_of_dvd_of_lt gd x.isLt
        exact False.elim ((Fin.val_ne_zero_iff.mpr hx) zero)
    have yd := gx.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero rel)
    apply Fin.ext
    simpa using Nat.eq_zero_of_dvd_of_lt yd y.isLt

private theorem cancel {p : Nat} [NeZero p] (hp : Prime p) {a x y : Fin p}
    (ha : a ≠ 0) (eq : a*x=a*y) : x=y := by
  have prod0 : a*(x-y)=0 := by grobner
  rcases mul_zero hp prod0 with z|z
  · exact False.elim (ha z)
  · grobner

theorem solve_linear {p : Nat} [NeZero p] (hp : Prime p) (d z : Fin p) (hd : d ≠ 0) :
    ∃ u, d*u=z := onto (fun u => d*u) (fun e => cancel hp hd e) z

/-- Choose one representative from each pair ±x, including the singleton 0. -/
def half {p : Nat} (hp : 0<p) (i : Fin (p/2+1)) : Fin p := ⟨i.val,by have := i.isLt; omega⟩

theorem half_square_injective {p : Nat} [NeZero p] (hp : Prime p) (odd : p%2=1)
    {i j : Fin (p/2+1)}
    (eq : (half (by omega : 0<p) i)^2=(half (by omega : 0<p) j)^2) : i=j := by
  let x := half (by omega : 0<p) i
  let y := half (by omega : 0<p) j
  change x^2=y^2 at eq
  have prod0 : (x-y)*(x+y)=0 := by grobner
  rcases mul_zero hp prod0 with h|h
  · have eq' : x=y := by grobner
    exact Fin.ext (congrArg (fun z : Fin p => z.val) eq')
  · have eq' : x = -y := by grobner
    by_cases zero : y=0
    · have xz : x=0 := by grobner
      exact Fin.ext (congrArg (fun z : Fin p => z.val) (xz.trans zero.symm))
    · have vv := congrArg Fin.val eq'
      rw [Fin.val_neg,ite_eq_right zero] at vv
      change i.val = p-j.val at vv
      have := i.isLt
      have := j.isLt
      omega

/-- A fractional linear transformation is injective after clearing nonzero
denominators; no division of an element of Fin p is required. -/
private theorem mobius_injective {p : Nat} [NeZero p] (hp : Prime p) {a b c d k v w z : Fin p}
    (det : a*d-b*c ≠ 0) (unit : k ≠ 0)
    (left : (c*v+d)*z=k*(a*v+b)) (right : (c*w+d)*z=k*(a*w+b)) : v=w := by
  have h : k*((a*d-b*c)*(v-w))=0 := by grobner
  rcases mul_zero hp h with bad|good
  · exact False.elim (unit bad)
  · rcases mul_zero hp good with bad|diff
    · exact False.elim (det bad)
    · grobner

def form {R : Type} [CommRing R] (a b c d u v : R) : R :=
  (a*u^2+b*v^2)*(c*u^2+d*v^2)

/-- All odd prime finite fields: every unit twist has a point in the affine
chart v=1. Coefficient invertibility is not needed for this finite statement. -/
theorem finite_affine {p : Nat} [NeZero p] (hp : Prime p) (odd : p%2=1)
    (a b c d k : Fin p) (det : a*d-b*c ≠ 0) (hk : k ≠ 0) :
    ∃ u y : Fin p, y^2 = k*form a b c d u 1 := by
  by_cases root : ∃ u : Fin p, c*u^2+d=0
  · obtain ⟨u,h⟩ := root
    exact ⟨u,0,by unfold form; grobner⟩
  · let square := fun i : Fin (p/2+1) => (half (by omega : 0<p) i)^2
    have pick : ∀ i, ∃ z, (c*square i+d)*z=k*(a*square i+b) := by
      intro i
      apply solve_linear hp
      intro hz
      exact root ⟨_,hz⟩
    let ratio := fun i => Classical.choose (pick i)
    have rat : ∀ i, (c*square i+d)*ratio i=k*(a*square i+b) := fun i =>
      Classical.choose_spec (pick i)
    have ri : ∀ {i j}, ratio i=ratio j → i=j := by
      intro i j eq
      have right := rat j
      rw [← eq] at right
      exact half_square_injective hp odd (mobius_injective hp det hk (rat i) right)
    have hit : ∃ i j, ratio i=square j := by
      by_cases h : ∃ i j, ratio i=square j
      · exact h
      · let l := List.ofFn ratio ++ List.ofFn square
        have noDup : l.Nodup := by
          apply List.nodup_append.mpr
          refine ⟨distinct_image ratio ri,distinct_image square (fun e => half_square_injective hp odd e),?_⟩
          intro x hx y hy e
          obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
          obtain ⟨j,hj⟩ := List.mem_ofFn.mp hy
          exact h ⟨i,j,hi.trans (e.trans hj.symm)⟩
        have le := length_bound (r := List.finRange p) noDup (fun x _ => List.mem_finRange x)
        simp [l,List.length_ofFn] at le
        omega
    obtain ⟨i,j,he⟩ := hit
    let u := half (by omega : 0<p) i
    let v := half (by omega : 0<p) j
    have eq := rat i
    rw [he] at eq
    change (c*u^2+d)*v^2=k*(a*u^2+b) at eq
    exact ⟨u,(c*u^2+d)*v,by unfold form; grobner⟩

end BinaryQuartic

#print axioms BinaryQuartic.mul_zero
#print axioms BinaryQuartic.solve_linear
#print axioms BinaryQuartic.half_square_injective
#print axioms BinaryQuartic.finite_affine
