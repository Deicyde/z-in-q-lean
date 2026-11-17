import ManuscriptArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Numeric conclusions of the two earlier V15 five-contact estimates.
All three bounds use the same marked rationals, contact valuations, bad primes,
and rational height. The proof of the cubic estimate in the manuscript also uses
geometric constructions from the earlier sections. The implications below concern
the two displayed parameter-height inequalities. -/
namespace ManuscriptV15.Arithmetic
open scoped BigOperators

/-- V15, line 7641. -/
noncomputable def Hstar : ℝ :=
  2*((4608:ℝ)^165888+6^100)*(badProduct:ℝ)^24+128

/-- V15, line 10009. -/
noncomputable def H19 : ℝ :=
  2*((2:ℝ)^109*210^1800)*(badProduct:ℝ)^19+128

def Height24Parameters : Prop :=
  ∀ a : ℚ, ¬ marked a → ratHeight a ≤ Hstar*(M5 a : ℝ)^24

def Height19Parameters : Prop :=
  ∀ a : ℚ, ¬ marked a → ratHeight a ≤ H19*(M5 a : ℝ)^19

/-- V15 hyp:o8-height (line 7651), with its stated binary logarithm. -/
def O8Height : Prop := Height24Parameters ∧ Real.logb 2 Hstar < 4783227

/-- V15 thm:quartic-height19 (line 10005), with its stated binary logarithm. -/
def QuarticHeight19 : Prop := Height19Parameters ∧ Real.logb 2 H19 < 2093966

private theorem bad_one_le : (1:ℝ) ≤ badProduct := by
  have h : 0 < badProduct := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  exact_mod_cast h

private theorem contacts_one_le (a : ℚ) : (1:ℝ) ≤ M5 a := by
  have h : 0 < M5 a := Finset.prod_pos fun p hp => ((mem_contact_iff a p).mp hp).2.1.pos
  exact_mod_cast h

private abbrev D : ℝ := (19:ℝ)*(4608*210^300)

private theorem cubic_constant_le : C3 ≤ D*(badProduct:ℝ)^4 := by
  let b : ℝ := badProduct
  have hb : 1 ≤ b := bad_one_le
  have hlog : Real.log b ≤ b := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc C3 = D*b^3*Real.log b := rfl
       _ ≤ D*b^3*b := mul_le_mul_of_nonneg_left hlog (mul_nonneg (by positivity : 0≤D) (by positivity))
       _ = D*b^4 := by rw [pow_succ b 3,mul_assoc]

private theorem D_le_19 : D ≤ (2:ℝ)^109*210^1800 := by
  have hinit : (19:ℝ)*4608 ≤ 2^17 := by norm_num
  have hfirst := hinit.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 17≤109))
  change (19:ℝ)*(4608*210^300) ≤ _
  rw [←mul_assoc]
  exact mul_le_mul hfirst (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤210) (by decide : 300≤1800))
    (by positivity) (by positivity)

private theorem D_le_star : D ≤ (4608:ℝ)^165888 := by
  calc D = (19*4608)*210^300 := (mul_assoc ..).symm
       _ ≤ 4608^2*4608^300 := mul_le_mul (by norm_num)
         (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤210) (by norm_num : (210:ℝ)≤4608) 300)
         (by positivity) (by positivity)
       _ = 4608^(2+300) := (pow_add ..).symm
       _ ≤ 4608^165888 := pow_le_pow_right₀ (by norm_num) (by decide : 2+300≤165888)

private theorem coefficient_le {d a b : ℝ} {k : ℕ}
    (hd : 0≤d) (hda : d≤a) (hb : 1≤b) (hk : 4≤k) :
    d*b^4 ≤ 2*a*b^k+128 := by
  have hb0 : 0≤b := by linarith
  have h := mul_le_mul hda (pow_le_pow_right₀ hb hk) (pow_nonneg hb0 4) (hd.trans hda)
  have h0 := mul_nonneg (hd.trans hda) (pow_nonneg hb0 k)
  linarith

private theorem cubic_to_power {h m c A : ℝ} {k : ℕ} (hm : 1≤m) (hc : 0≤c)
    (hcA : c≤A) (hk : 4≤k) (bound : h≤c*m^3*(1+Real.log m)) : h≤A*m^k := by
  have hm0 : 0 < m := by linarith
  have hb : 1+Real.log m ≤ m := by linarith [Real.log_le_sub_one_of_pos hm0]
  calc h ≤ c*m^3*(1+Real.log m) := bound
       _ ≤ c*m^3*m := mul_le_mul_of_nonneg_left hb (mul_nonneg hc (pow_nonneg hm0.le 3))
       _ = c*m^4 := by rw [pow_succ m 3,mul_assoc]
       _ ≤ A*m^k := mul_le_mul hcA (pow_le_pow_right₀ hm hk) (pow_nonneg hm0.le 4) (hc.trans hcA)

/-- Once the cubic five-contact estimate is known, both predecessor
parameter inequalities follow by comparison of their stated constants. -/
theorem predecessorParameters_of_fiveContact (h : FiveContact) :
    Height19Parameters ∧ Height24Parameters := by
  have hc : 0≤C3 := mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤D) (by positivity))
    (Real.log_nonneg bad_one_le)
  have h19 : C3 ≤ H19 := cubic_constant_le.trans
    (coefficient_le (by positivity : 0≤D) D_le_19 bad_one_le (by decide : 4≤19))
  have hstar : C3 ≤ Hstar := cubic_constant_le.trans (coefficient_le (by positivity : 0≤D)
    (D_le_star.trans (le_add_of_nonneg_right (by positivity : (0:ℝ)≤6^100))) bad_one_le
    (by decide : 4≤24))
  exact ⟨fun a ha => cubic_to_power (contacts_one_le a) hc h19 (by decide) (h.2 a ha),
    fun a ha => cubic_to_power (contacts_one_le a) hc hstar (by decide) (h.2 a ha)⟩

/-- Finite input for the printed binary logarithms (V15 lines 8757–8767 and
10155–10159). The following Magma 2.28-3 computation checks this proposition
independently. It remains an explicit hypothesis of the Lean logarithm theorem.

```magma
P := PrimesInInterval(2,76176);
B := &*P;
assert #P eq 7499 and P[#P] eq 76163;
assert 2^109444 le B and B lt 2^109445;
H19 := 2*(2^109*210^1800)*B^19+128;
Hstar := 2*(4608^165888+6^100)*B^24+128;
assert H19 lt 2^2093966 and Hstar lt 2^4783227;
print "7499 primes, largest 76163, B has 109445 bits";
print "H19 < 2^2093966 and Hstar < 2^4783227: PASS";
quit;
``` -/
def PrimorialBitBound : Prop := badProduct < (2:ℕ)^109445

private theorem nineteen_small {a b : ℝ} (h : 64<a*b) : 2*a*b+128 < 4*(a*b) := by linarith

private theorem star_small {a c b : ℝ} (ha : 128≤a) (hca : c≤a) (hb : 1≤b) :
    2*(a+c)*b+128 < 8*(a*b) := by
  have hb0 : 0≤b := by linarith
  have hab := mul_le_mul_of_nonneg_left hb (by linarith : 0≤a)
  have hcb := mul_le_mul_of_nonneg_right hca hb0
  linarith

/-- The printed bit bounds reduce to one bound on the product of the
7,499 small primes; neither threshold requires large real exponentials. -/
theorem predecessorBitBounds (hl : PrimorialBitBound) :
    H19 < (2:ℝ)^2093966 ∧ Hstar < (2:ℝ)^4783227 := by
  let b : ℝ := badProduct
  have hb : 1 ≤ b := bad_one_le
  have hupper : b ≤ (2:ℝ)^109445 := by
    calc (badProduct:ℝ) ≤ ((2^109445 : ℕ):ℝ) := Nat.cast_le.mpr hl.le
         _ = (2:ℝ)^109445 := by rw [Nat.cast_pow]; norm_num only [Nat.cast_ofNat]
  have h2 : (128:ℝ) ≤ 2^109 :=
    (show (128:ℝ)=(2:ℝ)^7 by norm_num).le.trans
      (pow_le_pow_right₀ (by norm_num) (by decide : 7≤109))
  have h210 : (1:ℝ)≤210^1800 := one_le_pow₀ (by norm_num)
  have h64 : 64<((2:ℝ)^109*210^1800)*b^19 := by
    have hA : (128:ℝ) ≤ 2^109*210^1800 := by
      have h := mul_le_mul h2 h210 (by norm_num : (0:ℝ)≤1) (by positivity)
      simpa only [mul_one] using h
    have h := mul_le_mul hA (one_le_pow₀ hb (n:=19)) (by norm_num : (0:ℝ)≤1) (by positivity)
    exact (by norm_num : (64:ℝ)<128).trans_le (by simpa only [mul_one] using h)
  have hbase : (210:ℝ)^1800 ≤ (2^8)^1800 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num : (210:ℝ)≤2^8) _
  have hA : (4608:ℝ)^165888 ≤ (2^13)^165888 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num : (4608:ℝ)≤2^13) _
  have hA128 : (128:ℝ) ≤ 4608^165888 :=
    (by norm_num : (128:ℝ)≤4608^1).trans (pow_le_pow_right₀ (by norm_num) (by decide : 1≤165888))
  have hA6 : (6:ℝ)^100 ≤ 4608^165888 :=
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6) (by norm_num : (6:ℝ)≤4608) 100).trans
      (pow_le_pow_right₀ (by norm_num) (by decide : 100≤165888))
  constructor
  · calc H19 < 4*(((2:ℝ)^109*210^1800)*b^19) := nineteen_small h64
         _ ≤ (2:ℝ)^2*((2^109*(2^8)^1800)*(2^109445)^19) := by
           rw [show (4:ℝ)=2^2 by norm_num]
           exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hbase (by positivity))
             (pow_le_pow_left₀ (zero_le_one.trans hb) hupper _) (by positivity) (by positivity)) (by positivity)
         _ = 2^2093966 := by simp only [←pow_mul,←pow_add]
  · calc Hstar < 8*((4608:ℝ)^165888*b^24) :=
           star_small hA128 hA6 (one_le_pow₀ hb)
         _ ≤ (2:ℝ)^3*((2^13)^165888*(2^109445)^24) := by
           rw [show (8:ℝ)=2^3 by norm_num]
           exact mul_le_mul_of_nonneg_left (mul_le_mul hA (pow_le_pow_left₀ (zero_le_one.trans hb) hupper _)
             (by positivity) (by positivity)) (by positivity)
         _ = 2^4783227 := by simp only [←pow_mul,←pow_add]

private theorem logb_bound {x : ℝ} (hx : 0<x) (n : ℕ) (h : x<(2:ℝ)^n) :
    Real.logb 2 x < (n:ℝ) := by
  apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hx).mpr
  simpa only [Real.rpow_natCast] using h

theorem predecessorHeights_of_fiveContact (h : FiveContact) (bits : PrimorialBitBound) :
    QuarticHeight19 ∧ O8Height := by
  obtain ⟨p19,p24⟩ := predecessorParameters_of_fiveContact h
  obtain ⟨b19,b24⟩ := predecessorBitBounds bits
  exact ⟨⟨p19,logb_bound (by dsimp [H19]; positivity) 2093966 b19⟩,
    ⟨p24,logb_bound (by dsimp [Hstar]; positivity) 4783227 b24⟩⟩

end ManuscriptV15.Arithmetic
#print axioms ManuscriptV15.Arithmetic.predecessorParameters_of_fiveContact
#print axioms ManuscriptV15.Arithmetic.predecessorBitBounds
#print axioms ManuscriptV15.Arithmetic.predecessorHeights_of_fiveContact
