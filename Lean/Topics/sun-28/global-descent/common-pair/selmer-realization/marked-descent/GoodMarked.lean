import MarkedLocal
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization ZInQ.RouteK.Selmer
open Polynomial

private theorem find_parameter (p : ℕ) [Fact p.Prime] (big : 3<p)
    (q b : ZMod p) (qn : ¬IsSquare q) (bn : ¬IsSquare b) :
    ∃ t : ZMod p, t≠0 ∧ b*(t^2-q)*(t^2-9*q)≠0 ∧ IsSquare (b*(t^2-q)*(t^2-9*q)) := by
  have hp:=Fact.out (p:=Nat.Prime p)
  have q0 : q≠0 := fun h=>qn (h ▸ IsSquare.zero)
  have b0 : b≠0 := fun h=>bn (h ▸ IsSquare.zero)
  have three : (3:ZMod p)≠0 := by
    change ((3:ℕ):ZMod p)≠0;rw [ne_eq,ZMod.natCast_eq_zero_iff];exact Nat.not_dvd_of_pos_of_lt (by decide) big
  have two : (2:ZMod p)≠0 := by
    change ((2:ℕ):ZMod p)≠0;rw [ne_eq,ZMod.natCast_eq_zero_iff];exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have nine : (9:ZMod p)≠0 := by rw [show (9:ZMod p)=3^2 by ring];exact pow_ne_zero 2 three
  have four : (8:ZMod p)≠0 := by rw [show (8:ZMod p)=2^3 by ring];exact pow_ne_zero 3 two
  have narrow : 2*(p/2)<p := by obtain ⟨k,h⟩:=hp.odd_of_ne_two (by omega);omega
  let m:=p/2
  have mp : m≠0 := by dsimp [m];omega
  have mr : (m:ZMod p)≠0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff];apply Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero mp)
    dsimp [m];omega
  let f : (ZMod p)[X] := (Polynomial.X-Polynomial.C q)^m-(Polynomial.X-Polynomial.C (9*q))^m
  have deg : f.natDegree ≤ m := by
    apply (natDegree_sub_le ..).trans
    simp only [natDegree_pow,natDegree_X_sub_C,mul_one,le_refl,max_self]
  have f0 : f≠0 := by
    intro H
    have eq:=sub_eq_zero.mp H
    have co:=congrArg Polynomial.nextCoeff eq
    rw [Monic.nextCoeff_pow (monic_X_sub_C _) _,Monic.nextCoeff_pow (monic_X_sub_C _) _,
      nextCoeff_X_sub_C,nextCoeff_X_sub_C] at co
    simp only [nsmul_eq_mul] at co
    exact (mul_ne_zero (mul_ne_zero four mr) q0) (by linear_combination co)
  have exists_t : ∃ t : ZMod p, f.eval (t^2)≠0 := by
    by_contra! h
    have gcd : (f.comp (Polynomial.X^2)).natDegree<p := by
      apply natDegree_comp_le.trans_lt
      simp only [natDegree_X_pow]
      omega
    have H : f.comp (Polynomial.X^2)=0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
      · intro t;simpa using h t
      · simpa [ZMod.card] using gcd
    rcases Polynomial.comp_eq_zero_iff.mp H with hf|⟨_,hc⟩
    · exact f0 hf
    · have d:=congrArg Polynomial.natDegree hc
      simp at d
  obtain ⟨t,h⟩:=exists_t
  have distinct : (t^2-q)^m≠(t^2-9*q)^m := by simpa [f,sub_ne_zero] using h
  have t0 : t≠0 := by
    intro t0;subst t
    have ep := (ZMod.euler_criterion p nine).mp (show IsSquare (9:ZMod p) from ⟨3,by ring⟩)
    apply distinct
    simp only [zero_pow (by decide : 2≠0),zero_sub,show -(9*q)=9*(-q) by ring,mul_pow]
    rw [show (9:ZMod p)^m=1 from ep,one_mul]
  have h₁ : t^2-q≠0 := fun e=>qn ⟨t,by linear_combination -e⟩
  have h₂ : t^2-9*q≠0 := by
    intro e;apply qn;use t/3;field_simp;linear_combination -e
  refine ⟨t,t0,mul_ne_zero (mul_ne_zero b0 h₁) h₂,?_⟩
  rw [ZMod.euler_criterion p (mul_ne_zero (mul_ne_zero b0 h₁) h₂),mul_pow,mul_pow]
  have eb : b^m= -1 := (ZMod.pow_div_two_eq_neg_one_or_one p b0).resolve_left
    (fun eq=>bn ((ZMod.euler_criterion p b0).mpr eq))
  rcases ZMod.pow_div_two_eq_neg_one_or_one p h₁ with e1|e1 <;>
    rcases ZMod.pow_div_two_eq_neg_one_or_one p h₂ with e2|e2 <;>
    first | exact (distinct (e1.trans e2.symm)).elim | change b^m*(t^2-q)^m*(t^2-9*q)^m=1;rw [eb,e1,e2];ring

theorem fixed_good_places (p : ℕ) [Fact p.Prime] (good : ¬ p ∣ 6*n) : Cover ℚ_[p] n mark 1 := by
  have big : 3<p := by
    by_contra! h
    have hp:=Fact.out (p:=Nat.Prime p)
    interval_cases p <;> first | exact good (by decide) | norm_num at hp
  have odd : p≠2 := by omega
  let b : ℤ:=526361
  let q : ℤ:=25815704738179
  have split : 6*n=6*(b*q).natAbs := by decide
  have units : ¬(p:ℤ)∣b ∧ ¬(p:ℤ)∣q := by
    constructor <;> intro h <;> apply good <;> rw [split] <;> apply dvd_mul_of_dvd_right
    · exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_of_dvd_left h q)
    · exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_of_dvd_right h b)
  by_cases hb : IsSquare (b:ZMod p)
  · exact cover_of_square (isSquare_intCast_of_residue odd units.1 hb)
  by_cases hq : IsSquare (q:ZMod p)
  · exact cover_of_square_multiplier (isSquare_intCast_of_residue odd units.2 hq)
  obtain ⟨t,tn,unit,square⟩:=find_parameter p big q b hq hb
  let T:ℤ:=t.val
  have lift : (T:ZMod p)=t := by simp [T]
  let A:=b*(T^2-q)*(T^2-9*q)
  have residue : (A:ZMod p)=(b:ZMod p)*(t^2-q)*(t^2-9*q) := by push_cast [A];rw [lift]
  have Au : ¬(p:ℤ)∣A := by
    intro e
    exact unit (residue.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr e))
  obtain ⟨s,S⟩:=isSquare_intCast_of_residue odd Au (residue.symm ▸ square)
  have Tn : (T:ℚ_[p])≠0 := by
    have nz:T≠0 := fun H => tn (lift.symm.trans (by rw [H,Int.cast_zero]))
    exact_mod_cast nz
  let U:ℚ_[p]:=(T^2-3*q)/(2*T)
  let V:ℚ_[p]:=(T^2+3*q)/(2*T)
  have L : (n:ℚ_[p])=(b:ℚ_[p])*(q:ℚ_[p]) := by
    change ((13588380161692636619:ℕ):ℚ_[p])=_
    norm_num [b,q]
  have bound : (b:ℚ_[p])*(T^2-q)*(T^2-9*q)=s*s := by
    simpa [A] using S
  refine ⟨U,s/(2*T),V,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩ <;> rw [L] <;>
    simp only [Int.cast_one,one_pow,one_mul,mul_one] <;> change (b:ℚ_[p])*_ - _=_
  · dsimp [U];field_simp [Tn];linear_combination bound
  · dsimp [U,V];field_simp [Tn];ring

theorem fixed_membership : (mark,1)∈localClasses n := by
  refine ⟨?_,squarefree_one, fixed_archimedean,fun p _=>?_⟩
  · change Squarefree (526361:ℤ)
    apply Int.squarefree_natCast.mpr
    change Squarefree (11*(109*439):ℕ)
    exact Nat.squarefree_mul_iff.mpr ⟨by decide,(by norm_num : Nat.Prime 11).squarefree,
      Nat.squarefree_mul_iff.mpr ⟨by decide,(by norm_num : Nat.Prime 109).squarefree,(by norm_num : Nat.Prime 439).squarefree⟩⟩
  · by_cases bad : p∣6*n
    · exact fixed_bad_primes p bad
    · exact fixed_good_places p bad
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.fixed_good_places
#print axioms Sun28.MarkedDescent.fixed_membership
