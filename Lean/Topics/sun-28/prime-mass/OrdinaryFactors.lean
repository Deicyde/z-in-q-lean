import PrimeSummation

namespace Sun28.PrimeMass
open Finset
noncomputable section
open scoped Classical
variable {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℕ} [Fact p.Prime]

/-- Permitted first coordinates for a fixed second coordinate. -/
def permitted (c : ι → ZMod p) (v : ZMod p) : Finset (ZMod p) :=
  ((univ.image c).image (fun a => -(a*v^2)))ᶜ

omit [Nonempty ι] in
theorem mem_permitted {c : ι → ZMod p} {u v : ZMod p} :
    u ∈ permitted c v ↔ ∀ i, u+c i*v^2 ≠ 0 := by
  classical
  simp [permitted, add_eq_zero_iff_eq_neg, eq_comm]

theorem permitted_card (c : ι → ZMod p) (v : ZMod p) :
    (permitted c v).card = if v=0 then p-1 else p-(univ.image c).card := by
  classical
  rw [permitted,Finset.card_compl,ZMod.card]
  by_cases h : v=0
  · subst v
    have ne : (univ.image c).Nonempty := univ_nonempty.image c
    simp [Finset.image_const ne]
  · rw [ite_eq_right h,Finset.card_image_of_injective]
    intro a b eq
    exact mul_right_cancel₀ (pow_ne_zero _ h) (neg_injective eq)

theorem ordinary_count (c : ι → ZMod p) :
    (∑ v : ZMod p,(permitted c v).card) = (p-1)*(p+1-(univ.image c).card) := by
  classical
  have le : (univ.image c).card ≤ p := by simpa using (card_le_univ (univ.image c))
  rw [←Finset.add_sum_erase _ _ (mem_univ (0:ZMod p)),permitted_card,ite_eq_left rfl]
  have each (v : ZMod p) (hv : v ∈ univ.erase (0:ZMod p)) :
      (permitted c v).card = p-(univ.image c).card := by
    rw [permitted_card,ite_eq_right (ne_of_mem_erase hv)]
  rw [sum_congr rfl each,sum_const,card_erase_of_mem (mem_univ _),card_univ,ZMod.card,nsmul_eq_mul]
  rw [show p+1-(univ.image c).card=(p-(univ.image c).card)+1 by omega]
  simp only [Nat.cast_id]
  ring

/-- The local factor for primality of all the rational forms. -/
def beta (c : ι → ZMod p) : ℝ :=
  (∑ v : ZMod p,(permitted c v).card : ℕ) / (p:ℝ)^2 / (1-1/(p:ℝ))^(Fintype.card ι)

private theorem power_bound (k : ℕ) {x : ℝ} (x0 : 0 ≤ x) (x1 : x ≤ 1) :
    (1-x)^k ≤ 1-(k:ℝ)*x+((k:ℝ)*x)^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    apply (mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr x1)).trans
    push_cast
    nlinarith only [mul_nonneg (sq_nonneg ((k:ℝ)*x)) x0, mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sq_nonneg x),sq_nonneg x]

theorem beta_large (c : ι → ZMod p) (hp : 2*Fintype.card ι ≤ p) :
    1-2*(Fintype.card ι:ℝ)^2/(p:ℝ)^2 ≤ beta c := by
  let k := Fintype.card ι
  let n := (univ.image c).card
  let x : ℝ := 1/(p:ℝ)
  have pp := (Fact.out : p.Prime)
  have pr : (0:ℝ)<p := by exact_mod_cast pp.pos
  have large : 2*(k:ℝ)≤p := by exact_mod_cast hp
  have small : (1:ℝ) < p := by exact_mod_cast pp.one_lt
  have xpos : 0 < x := by dsimp [x]; positivity
  have x1 : x < 1 := (div_lt_one pr).mpr small
  have np : n ≤ p := by simpa [n] using (card_le_univ (univ.image c))
  have nk : n ≤ k := (card_image_le).trans_eq (by simp [k])
  have np1 : 1 ≤ n := (univ_nonempty.image c).card_pos
  have dk : 0 ≤ (k:ℝ)*x := by positivity
  have kx : (k:ℝ)*x ≤ 1/2 := by
    dsimp [x]; rw [mul_one_div,div_le_iff₀ pr]; linarith
  let den := (1-x)^k
  have dp : 0 < den := pow_pos (sub_pos.mpr x1) _
  have half : 1/2 ≤ den := by
    have be := one_add_mul_le_pow (show -2 ≤ -x by linarith) k
    change (1:ℝ)/2 ≤ (1-x)^k
    have ee : 1 + (k:ℝ)*(-x) ≤ (1-x)^k := by simpa [sub_eq_add_neg] using be
    linarith
  have num : 1-(k:ℝ)*x ≤ ((∑ v : ZMod p,(permitted c v).card : ℕ):ℝ)/(p:ℝ)^2 := by
    rw [ordinary_count,Nat.cast_mul,Nat.cast_sub pp.one_le,Nat.cast_sub (by omega : n≤p+1)]
    push_cast
    change _ ≤ ((p:ℝ)-1)*(((p:ℝ)+1)-(n:ℝ))/(p:ℝ)^2
    have nk' : (n:ℝ)≤k := by exact_mod_cast nk
    have n1 : 1≤(n:ℝ) := by exact_mod_cast np1
    dsimp [x]; field_simp
    nlinarith only [mul_le_mul_of_nonneg_right nk' pr.le,n1]
  have loss := mul_le_mul_of_nonneg_right half (show 0 ≤ 2*((k:ℝ)*x)^2 by positivity)
  have top := power_bound k xpos.le x1.le
  change _ ≤ _ / den
  apply (le_div_iff₀ dp).mpr
  apply le_trans _ num
  have eq : 2*(Fintype.card ι:ℝ)^2/(p:ℝ)^2 = 2*((k:ℝ)*x)^2 := by dsimp [k,x]; ring
  rw [eq]
  change (1-2*((k:ℝ)*x)^2)*den ≤ _
  change den ≤ _ at top
  nlinarith only [loss,top]

end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.mem_permitted
#print axioms Sun28.PrimeMass.permitted_card
#print axioms Sun28.PrimeMass.ordinary_count
#print axioms Sun28.PrimeMass.beta_large
