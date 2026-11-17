import ElementaryLocal

namespace Sun28.ConeEuler.Elementary
open Finset ArithmeticFunction
noncomputable section

def signedInv (d : ℕ) : ℝ := (chi d)/d

private theorem inv_even {n : ℕ} (h : n%2=0) : signedInv n=0 := by
  change ((ZMod.χ₄ (n:ZMod 4):ℤ):ℝ)/n=0
  rw [ZMod.χ₄_nat_eq_if_mod_four];simp [h]

private theorem inv_one {n : ℕ} (h : n%4=1) : signedInv n=1/(n:ℝ) := by
  change ((ZMod.χ₄ (n:ZMod 4):ℤ):ℝ)/n=1/n
  rw [ZMod.χ₄_nat_one_mod_four h];norm_num

private theorem inv_three {n : ℕ} (h : n%4=3) : signedInv n= -1/(n:ℝ) := by
  change ((ZMod.χ₄ (n:ZMod 4):ℤ):ℝ)/n= -1/n
  rw [ZMod.χ₄_nat_three_mod_four h];norm_num

theorem reciprocal_character (n : ℕ) (hn : 0<n) :
    2/3≤∑ d∈range (n+1),signedInv d := by
  let F:=fun t : ℕ => ∑ d∈range (t+1),signedInv d
  have block (j : ℕ) : F (4*j) ≤ F (4*(j+1)) := by
    have a : (0:ℝ)<4*j+1 := by positivity
    have part : 1/((4:ℝ)*j+3)≤1/(4*j+1) := one_div_le_one_div_of_le a (by linarith)
    have ext : 4*(j+1)+1=4*j+1+4 := by omega
    dsimp only [F];rw [ext,sum_range_add (f:=signedInv) (4*j+1) 4]
    apply le_add_of_nonneg_right
    simp only [sum_range_succ,sum_range_zero,zero_add,Nat.add_zero]
    rw [inv_one (by omega),inv_even (by omega),inv_three (by omega),inv_even (by omega)]
    push_cast
    rw [show 4*(j:ℝ)+1+2=4*j+3 by ring]
    simpa only [add_zero,neg_div,sub_eq_add_neg] using sub_nonneg.mpr part
  have base : ∀ j : ℕ,2/3 ≤ F (4*(j+1)) := by
    intro j;induction j with
    | zero => norm_num [F,signedInv,chi,ZMod.χ₄_nat_eq_if_mod_four,sum_range_succ]
    | succ j ih => exact ih.trans (block (j+1))
  change 2/3≤F n
  have step (j : ℕ) : F (4*j)≤F (4*j+1) ∧ F (4*j)≤F (4*j+2) ∧ F (4*j+3)=F (4*(j+1)) := by
    have h : 4*(j+1)=4*j+3+1 := by omega
    have one : F (4*j+1)=F (4*j)+1/((4:ℝ)*j+1) := by
      dsimp only [F];rw [sum_range_succ (f:=signedInv) (4*j+1),inv_one (by omega)];push_cast;rfl
    have two : F (4*j+2)=F (4*j+1) := by
      dsimp only [F];rw [sum_range_succ (f:=signedInv) (4*j+2),inv_even (by omega),add_zero]
    have four : F (4*j+3)=F (4*(j+1)) := by
      rw [h];dsimp only [F];rw [sum_range_succ (f:=signedInv) (4*j+3+1),inv_even (by omega),add_zero]
    rw [two,one];exact ⟨le_add_of_nonneg_right (by positivity),le_add_of_nonneg_right (by positivity),four⟩
  let j:=n/4
  have eq : n=4*j+n%4 := by dsimp [j];omega
  rcases eq_or_ne j 0 with zero|non
  · have h : n≤3 := by dsimp [j] at zero;omega
    interval_cases n <;> norm_num [F,signedInv,chi,ZMod.χ₄_nat_eq_if_mod_four,sum_range_succ]
  · have h : 2/3≤F (4*j) := by simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr non)] using base (j-1)
    obtain ⟨a,b,c⟩:=step j
    have d : F (4*j+3)≥2/3 := c.symm ▸ base j
    have rem := Nat.mod_lt n (by decide : 0<4)
    rcases (show n=4*j ∨ n=4*j+1 ∨ n=4*j+2 ∨ n=4*j+3 by omega) with e|e|e|e
    · rwa [e]
    · rw [e];exact h.trans a
    · rw [e];exact h.trans b
    · rwa [e]

theorem multiples (n e : ℕ) (he : 0<e) :
    ((Icc 1 n).filter (e∣·))=(Icc 1 (n/e)).image (fun d=>e*d) := by
  ext m
  simp only [mem_filter,mem_Icc,mem_image]
  constructor
  · rintro ⟨⟨lo,hi⟩,⟨d,rfl⟩⟩
    refine ⟨d,⟨?_,(Nat.le_div_iff_mul_le he).mpr (by simpa [Nat.mul_comm] using hi)⟩,rfl⟩
    apply Nat.pos_of_ne_zero
    rintro rfl;simp at lo
  · rintro ⟨d,⟨lo,hi⟩,rfl⟩
    exact ⟨⟨Nat.mul_pos he lo,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le he).mp hi⟩,dvd_mul_right _ _⟩

theorem convolution_row (n : ℕ) :
    (∑ m∈Icc 1 n,gaussian m/m) =
    ∑ e∈Icc 1 n, (∑ d∈range (n/e+1),signedInv d)/(e:ℝ) := by
  let U:=Icc 1 n
  have row (m : ℕ) (hm : m∈U) : gaussian m /m=∑ e∈U, (if e∣m then chi (m/e)/(m:ℝ) else 0) := by
    have nz : m≠0:=by have h:=(mem_Icc.mp hm).1;omega
    change ((zeta:ArithmeticFunction ℝ)*chi) m / m=_
    rw [coe_zeta_mul_apply,←Nat.sum_div_divisors m (fun d=>chi d),sum_div,←sum_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors,mem_filter,mem_Icc,U]
    constructor
    · rintro ⟨dvd,_⟩;exact ⟨⟨Nat.pos_of_dvd_of_pos dvd (Nat.pos_of_ne_zero nz),(Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dvd).trans (mem_Icc.mp hm).2⟩,dvd⟩
    · exact fun h=>⟨h.2,nz⟩
  change (∑ m∈U,gaussian m/m)=_
  rw [sum_congr rfl row,sum_comm]
  apply sum_congr rfl
  intro e he
  have pos:=(mem_Icc.mp he).1
  rw [←sum_filter]
  change (∑ m∈ (Icc 1 n).filter (e∣·),chi (m/e)/(m:ℝ))=_
  rw [multiples n e pos,sum_image (by intro a _ b _ eq;exact Nat.eq_of_mul_eq_mul_left pos eq)]
  have addzero : (∑ d∈range (n/e+1),signedInv d)=(∑ d∈Icc 1 (n/e),signedInv d) := by
    rw [show range (n/e+1) = insert 0 (Icc 1 (n/e)) by
      ext d;cases d <;> simp]
    simp [signedInv]
  rw [addzero,sum_div]
  apply sum_congr rfl
  intro d _
  simp only [Nat.mul_div_cancel_left _ pos,Nat.cast_mul,signedInv]
  ring

theorem harmonic_gaussian (n : ℕ) :
    (2/3:ℝ)*(harmonic n:ℝ)≤∑ m∈Icc 1 n,gaussian m/m := by
  rw [convolution_row,harmonic_eq_sum_Icc,Rat.cast_sum,mul_sum]
  apply sum_le_sum
  intro e h
  have pos:=(mem_Icc.mp h).1
  have le:=(mem_Icc.mp h).2
  have q : 0<n/e := (Nat.le_div_iff_mul_le pos).mpr (by simpa)
  simpa only [Rat.cast_inv,Rat.cast_natCast,div_eq_mul_inv] using
    div_le_div_of_nonneg_right (reciprocal_character _ q) (Nat.cast_nonneg (α:=ℝ) e)

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.reciprocal_character
#print axioms Sun28.ConeEuler.Elementary.multiples
#print axioms Sun28.ConeEuler.Elementary.convolution_row
#print axioms Sun28.ConeEuler.Elementary.harmonic_gaussian
