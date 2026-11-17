import PrimitiveRoots
import QuarticPoints

namespace ZInQBlueprint.MarkedTorsion
open Height WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open ZInQBlueprint.OriginalConcentrated ZInQBlueprint.OriginalHeightCount
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open scoped Classical
noncomputable section
set_option maxRecDepth 12000
set_option exponentiation.threshold 1024
attribute [local irreducible] glazerConstant24

/-- Leading coefficients of the five cubic charts and the three coefficients of their monic models. -/
def k (j:Fin 5) : ℤ := ![823543,32,32,32,1] j
def a (j:Fin 5) : ℤ := ![-747054,-76521,-76489,311,-2402] j
def b (j:Fin 5) : ℤ := ![-63018333903,-23905728,-26353376,-10976,2401] j
def c (j:Fin 5) : ℤ := ![21703138331168,843308032,0,0,0] j

def model (j:Fin 5) (d:ℚ) := twist (a j:ℚ) (b j) (c j) d

theorem monic_chart (j:Fin 5) (t:ℚ) :
    F (a j:ℚ) (b j) (c j) ((k j:ℚ)*t) 1 = (k j:ℚ)^2*cubic j t := by
  fin_cases j <;> norm_num [a,b,c,k,cubic,F] <;> ring

private theorem scale_nonzero (j:Fin 5) : (k j:ℚ)≠0 := by fin_cases j <;> decide

/-- The actual rational point of each omitted-row twist. Its normalized abscissa is k times the chart. -/
theorem represented_point {s:ℚ} (off:offMarks s) (j:Fin 5) :
    ∃ P:(model j (signedTwist j s:ℚ)).toAffine.Point,
      Represents P ((k j:ℚ)*chart j s) 1 := by
  obtain ⟨y,yn,eq⟩:=point_on_twist off j
  let d:ℚ:=signedTwist j s
  have dn:d≠0 := by intro h;change y^2=d*_ at eq;rw [h,zero_mul] at eq;exact (pow_ne_zero 2 yn) eq
  let x:=d*((k j:ℚ)*chart j s)
  let Y:=d*(k j:ℚ)*y
  have Yn:Y≠0:=mul_ne_zero (mul_ne_zero dn (scale_nonzero j)) yn
  have e:Y^2=d^3*F (a j:ℚ) (b j) (c j) ((k j:ℚ)*chart j s) 1 := by
    rw [monic_chart];dsimp [Y];linear_combination (d*(k j:ℚ))^2*eq
  have ns:(model j d).toAffine.Nonsingular x Y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff',WeierstrassCurve.Affine.equation_iff]
    constructor
    · dsimp [model,twist,x];unfold F at e;linear_combination e
    · right;simp [model,twist,Yn]
  exact ⟨some x Y ns,by change d*_=x*1;simp [x]⟩

private theorem numerical (j:Fin 5) (i:Test) :
    0 < (test (a j) (b j) (c j) i 3 1).natAbs ∧
      (test (a j) (b j) (c j) i 3 1).natAbs ≤2^862 := by
  fin_cases j <;> cases i <;> decide

theorem translated_height {j:Fin 5} {d s:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point)
    (rep:Represents P ((k j:ℚ)*chart j s) 1)
    (ord:(4:ℕ) • P=0 ∨ (6:ℕ) • P=0 ∨ (8:ℕ) • P=0) :
    logHeight₁ ((k j:ℚ)*chart j s-3) ≤ 862 := by
  let z:=(k j:ℚ)*chart j s-3
  obtain ⟨i,eq⟩:=exponent_test dn (by norm_num : (1:ℚ)≠0) P rep ord
  have h:test (a j:ℚ) (b j) (c j) i (z+3) 1=0 := by simpa [z] using eq
  obtain ⟨num,den⟩:=rational_root z i h
  have values:=numerical j i
  have hnum:= (Nat.le_of_dvd values.1 num).trans values.2
  have hden:z.den≤3 := (Nat.le_of_dvd (show (top i).natAbs>0 by cases i <;> decide) den).trans
    (by cases i <;> decide)
  have bound:max z.num.natAbs z.den ≤ 2^862 := max_le hnum (hden.trans (by decide))
  change logHeight₁ z≤862
  rw [Rat.logHeight₁_eq_log_max]
  have hl:=Real.log_le_log (by exact_mod_cast z.den_pos.trans_le (le_max_right z.num.natAbs z.den) :
    0 < ((max z.num.natAbs z.den:ℕ):ℝ)) (by exact_mod_cast bound :
    ((max z.num.natAbs z.den:ℕ):ℝ)≤(2:ℝ)^862)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have two:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  linarith

theorem bounded_abscissa {j:Fin 5} {d s:ℚ} (dn:d≠0) (P:(model j d).toAffine.Point)
    (rep:Represents P ((k j:ℚ)*chart j s) 1)
    (ord:(4:ℕ) • P=0 ∨ (6:ℕ) • P=0 ∨ (8:ℕ) • P=0) : logHeight₁ s ≤ 900 := by
  let z:=(k j:ℚ)*chart j s-3
  have h:logHeight₁ z≤862:=translated_height dn P rep ord
  have hz:z+3=(k j:ℚ)*chart j s:=by dsimp [z];ring
  have shifted:=logHeight₁_add_le z (3:ℚ)
  rw [hz] at shifted
  have result:=logHeight₁_mul_le ((k j:ℚ)*chart j s) ((k j:ℚ)⁻¹)
  rw [mul_right_comm,mul_inv_cancel₀ (scale_nonzero j),one_mul,logHeight₁_inv] at result
  have th:logHeight₁ (chart j s)=logHeight₁ s := by
    unfold chart;split
    · exact logHeight₁_inv _
    · rfl
  have hk: logHeight₁ (k j:ℚ)≤20 := by
    rw [Rat.logHeight₁_eq_log_max]
    have bound : max (k j:ℚ).num.natAbs (k j:ℚ).den≤2^20 := by fin_cases j <;> decide
    have ll:=Real.log_le_log (by exact_mod_cast (k j:ℚ).den_pos.trans_le (le_max_right ..) :
      0<((max (k j:ℚ).num.natAbs (k j:ℚ).den:ℕ):ℝ)) (by exact_mod_cast bound :
      ((max (k j:ℚ).num.natAbs (k j:ℚ).den:ℕ):ℝ)≤(2:ℝ)^20)
    rw [Real.log_pow] at ll;norm_num only [Nat.cast_ofNat] at ll;linarith [Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]
  have three:logHeight₁ (3:ℚ)≤3 := by
    rw [Rat.logHeight₁_eq_log_max];norm_num;exact Real.log_le_self (by norm_num)
  have wt:totalWeight ℚ=1 := by rw [NumberField.totalWeight_eq_finrank,Module.finrank_self]
  rw [wt,Nat.cast_one,one_mul] at shifted
  rw [th] at result
  linarith [Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

/-- Mazur, Modular curves and the Eisenstein ideal, Theorem 8, for the five split cubics. -/
def FullTwoTorsionExponents : Prop := ∀ (j:Fin 5) (d:ℚ), d≠0 →
  ∀ P:(model j d).toAffine.Point, IsOfFinAddOrder P →
    (4:ℕ) • P=0 ∨ (6:ℕ) • P=0 ∨ (8:ℕ) • P=0

theorem five_infinite_orders (mazur:FullTwoTorsionExponents) {s:ℚ} (bad:failure s) (j:Fin 5) :
    ∃ P:(model j (signedTwist j s:ℚ)).toAffine.Point,
      Represents P ((k j:ℚ)*chart j s) 1 ∧ ¬IsOfFinAddOrder P := by
  obtain ⟨P,h⟩:=represented_point bad.1 j
  have dn:(signedTwist j s:ℚ)≠0 := by
    obtain ⟨y,yn,v⟩:=point_on_twist bad.1 j
    intro z;rw [z,zero_mul] at v;exact (pow_ne_zero 2 yn) v
  refine ⟨P,h,fun tor=>?_⟩
  have hh:=bounded_abscissa dn P h (mazur j _ dn P tor)
  let T:=heightRadical s.num s.den
  have pos : (1:ℝ)≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd s.num s.den))
  have large:(900:ℝ)≤2^810:=(by norm_num:(900:ℝ)≤2^10).trans (pow_le_pow_right₀ (by norm_num) (by decide))
  have lower := large.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ pos (n:=24)))
  exact (not_lt_of_ge (hh.trans (lower.trans (original_margin s.num s.den)))) bad.2
end
end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.monic_chart
#print axioms ZInQBlueprint.MarkedTorsion.represented_point
#print axioms ZInQBlueprint.MarkedTorsion.translated_height
#print axioms ZInQBlueprint.MarkedTorsion.bounded_abscissa
#print axioms ZInQBlueprint.MarkedTorsion.five_infinite_orders
