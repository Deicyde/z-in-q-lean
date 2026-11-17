import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! Unit twists of the two-factor detector quartic over a finite residue field. -/

namespace QuarticResidues
open Polynomial
variable {F : Type*} [Field F]

private theorem nonzero_of_nonsquare {a : F} (ha : ¬IsSquare a) : a ≠ 0 :=
  fun h => ha ⟨0, by simp [h]⟩

private theorem sub_square_ne {a : F} (ha : ¬IsSquare a) (x : F) : x^2-a ≠ 0 :=
  fun h => ha ⟨x, by simpa only [pow_two] using (sub_eq_zero.mp h).symm⟩

variable [Fintype F]

private theorem two_nonsquares (odd : ringChar F ≠ 2) {a b : F}
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) : IsSquare (a*b) := by
  have na := nonzero_of_nonsquare ha
  have nb := nonzero_of_nonsquare hb
  have ea := (FiniteField.pow_dichotomy odd na).resolve_left
    (fun e => ha ((FiniteField.isSquare_iff odd na).mpr e))
  have eb := (FiniteField.pow_dichotomy odd nb).resolve_left
    (fun e => hb ((FiniteField.isSquare_iff odd nb).mpr e))
  apply (FiniteField.isSquare_iff odd (mul_ne_zero na nb)).mpr
  rw [mul_pow, ea, eb]; simp

/-- Two distinct nonsquares give different quadratic characters at some square argument. -/
theorem exists_nonsquare_product (odd : ringChar F ≠ 2) {a b : F}
    (hab : a ≠ b) (ha : ¬IsSquare a) (hb : ¬IsSquare b) :
    ∃ x : F, ¬IsSquare ((x^2-a)*(x^2-b)) := by
  classical
  by_contra! allSquare
  let h := Fintype.card F / 2
  have hc := Fintype.one_lt_card (α := F)
  have hpos : 0<h := by dsimp [h]; omega
  let poly : F[X] := (X-C a)^h-(X-C b)^h
  have live : poly ≠ 0 := by
    intro hz
    have atA := congrArg (fun g : F[X] => g.eval a) hz
    have nonvanish : (a-b)^h ≠ 0 := pow_ne_zero h (sub_ne_zero.mpr hab)
    simp [poly, Nat.ne_of_gt hpos, nonvanish] at atA
  have degreeBound : poly.natDegree ≤ h := by
    unfold poly
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp [natDegree_pow])
  let squares := (Finset.univ : Finset F).image (fun x : F => x^2)
  have enough : Fintype.card F ≤ 2*squares.card := by
    let f : F[X] := X^2
    have deg : f.natDegree=2 := Polynomial.natDegree_X_pow 2
    have eval : (fun x : F => f.eval x) = (fun x : F => x^2) := by
      funext x; dsimp only [f]; rw [Polynomial.eval_pow,Polynomial.eval_X]
    have cnt := FiniteField.card_image_polynomial_eval (p := f) (by simp [f])
    rw [deg,eval] at cnt
    exact cnt
  have roots : squares.val ⊆ poly.roots := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (show y ∈ squares from hy)
    have na := sub_square_ne ha x
    have nb := sub_square_ne hb x
    have one := (FiniteField.isSquare_iff odd (mul_ne_zero na nb)).mp (allSquare x)
    rw [mul_pow] at one
    have invol : (x^2-b)^h * (x^2-b)^h=1 := by
      rcases FiniteField.pow_dichotomy odd nb with eq | eq <;> simpa only [h,eq] using
        (show (x^2-b)^(Fintype.card F/2)*(x^2-b)^(Fintype.card F/2)=1 by rw [eq]; simp)
    have equal : (x^2-a)^h=(x^2-b)^h := by
      calc
        _ = (x^2-a)^h*((x^2-b)^h*(x^2-b)^h) := by rw [invol,mul_one]
        _ = _ := by rw [← mul_assoc,show (x^2-a)^h*(x^2-b)^h=1 from one,one_mul]
    apply (Polynomial.mem_roots live).mpr
    simpa [Polynomial.IsRoot,poly] using sub_eq_zero.mpr equal
  have bound := (Polynomial.card_le_degree_of_subset_roots roots).trans degreeBound
  have parity := FiniteField.odd_card_of_char_ne_two odd
  dsimp only [h] at bound
  omega

/-- Every unit twist has a point with affine parameter and nonzero ordinate. -/
theorem unit_twist (odd : ringChar F ≠ 2) {a b u : F}
    (hab : a ≠ b) (ha : ¬IsSquare a) (hb : ¬IsSquare b) (hu : u ≠ 0) :
    ∃ x y : F, y ≠ 0 ∧ y^2=u*((x^2-a)*(x^2-b)) := by
  have obtainPoint (x : F) (sq : IsSquare (u*((x^2-a)*(x^2-b)))) :
      ∃ y : F, y ≠ 0 ∧ y^2=u*((x^2-a)*(x^2-b)) := by
    obtain ⟨y,hy⟩:=sq
    have nz := mul_ne_zero hu (mul_ne_zero (sub_square_ne ha x) (sub_square_ne hb x))
    refine ⟨y,fun yz => nz (by simpa [yz] using hy),?_⟩
    simpa [pow_two] using hy.symm
  by_cases sq : IsSquare u
  · refine ⟨0,obtainPoint 0 ?_⟩
    simpa using sq.mul (two_nonsquares odd ha hb)
  · obtain ⟨x,hx⟩:=exists_nonsquare_product odd hab ha hb
    exact ⟨x,obtainPoint x (two_nonsquares odd sq hx)⟩

/-- The specialization used by the rational scalar and all three comparison poles. -/
theorem detector_quartic (odd : ringChar F ≠ 2) {c u : F}
    (hc : ¬IsSquare c) (hd : ¬IsSquare (-(3*c))) (hu : u ≠ 0) :
    ∃ x y : F, y ≠ 0 ∧ y^2=u*((x^2-c)*(x^2+3*c)) := by
  have different : c ≠ -(3*c) := by
    intro e
    have h2 := Ring.two_ne_zero odd
    apply (mul_ne_zero (mul_ne_zero h2 h2) (nonzero_of_nonsquare hc))
    calc
      (2*2)*c = c-(-(3*c)) := by ring
      _ = 0 := sub_eq_zero.mpr e
  simpa only [sub_neg_eq_add] using unit_twist odd different hc hd hu

#print axioms exists_nonsquare_product
#print axioms detector_quartic
end QuarticResidues
