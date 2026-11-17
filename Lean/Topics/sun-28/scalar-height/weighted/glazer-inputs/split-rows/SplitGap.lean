import PairedUnits

/-! An integer gap between unequal squares controls the height without a unit equation. -/
namespace ZInQBlueprint.SplitRows
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance Sun28.HeightFibres
open ZInQ.RouteK Sun28.MinimalConductors
open private form_diff from BalancedUnits
noncomputable section
attribute [local irreducible] glazerConstant24
set_option maxRecDepth 12000

private theorem square_gap {u v : ℤ} (different : u^2≠v^2) :
    |u| ≤ |u^2-v^2| ∧ |v| ≤ |u^2-v^2| := by
  have nz : |u|≠|v| := by
    intro e
    exact different (by rw [←sq_abs u,←sq_abs v,e])
  have big (a b : ℤ) (h : b<a) (hb : 0≤b) : a≤a^2-b^2 := by
    have d : 1≤a-b := by omega
    have e:=mul_le_mul_of_nonneg_right d (show 0≤a+b by omega)
    nlinarith only [e,hb]
  rcases lt_or_gt_of_ne nz with h|h
  · have out:=big _ _ h (abs_nonneg u)
    have rev : |v|≤|u^2-v^2| := by
      have lower : |v| ≤ v^2-u^2 := by simpa only [sq_abs] using out
      exact lower.trans (by rw [abs_sub_comm];exact le_abs_self _)
    exact ⟨h.le.trans rev,rev⟩
  · have out:=big _ _ h (abs_nonneg v)
    have rev : |u|≤|u^2-v^2| := by
      have lower : |u| ≤ u^2-v^2 := by simpa only [sq_abs] using out
      exact lower.trans (le_abs_self _)
    exact ⟨rev,h.le.trans rev⟩

/-- For the parent squareclass match, the signed roots both lie below the nonzero difference. -/
theorem split_raw (R : ThreeRows) {A B d u v:ℤ} (off : ∀ i,oldForm i A B≠0)
    (matched : R.Match A B d u v) :
    let L:=det R.a R.b*oldForm R.center A B
    |d*u^2|≤L^2 ∧ |d*v^2|≤L^2 := by
  intro L
  have diff : d*(u^2-v^2)=L := by
    dsimp [L]
    linear_combination -matched.first + matched.second + form_diff R.center R.a R.b A B
  have nz : L≠0 := mul_ne_zero (det_ne R.ab) (off _)
  have dh : d≠0 := fun q=>nz (by rw [←diff,q,zero_mul])
  have du : u^2≠v^2 := fun q=>nz (by rw [←diff,q,sub_self,mul_zero])
  have h:=square_gap du
  have ad : 1≤|d| := by have := abs_pos.mpr dh;omega
  have adm : |d|≤|d|^2 := by nlinarith only [sq_nonneg (|d|-1),ad]
  have bound (w : ℤ) (small : |w|≤|u^2-v^2|) : |d*w^2|≤L^2 := by
    rw [abs_mul,abs_pow,←diff,mul_pow,←sq_abs d,←sq_abs (u^2-v^2)]
    exact mul_le_mul adm (pow_le_pow_left₀ (abs_nonneg _) small 2) (sq_nonneg _) (sq_nonneg _)
  exact ⟨bound u h.1,bound v h.2⟩

theorem split_height (R : ThreeRows) {A B d u v:ℤ} (off : ∀ i,oldForm i A B≠0)
    (matched : R.Match A B d u v) :
    pairLogHeight A B ≤ 2*numberLog (oldForm R.center A B)+47 := by
  let i:=R.a
  let j:=R.b
  let F:=oldForm R.center A B
  let L:=det i j*F
  have minor : det i j≠0 := det_ne R.ab
  have Fn : F≠0 := off _
  have Ln : L≠0 := mul_ne_zero minor Fn
  have Lzero : 0≤L^2 := sq_nonneg _
  have quot {m n : ℤ} (mn:m≠0) : |n|≤|m*n| := by
    rw [abs_mul];have one : (1:ℤ)≤|m| := by have := abs_pos.mpr mn;omega
    simpa only [one_mul] using mul_le_mul_of_nonneg_right one (abs_nonneg n)
  have h := split_raw R off matched
  have first : |oldForm i A B|≤L^2 := (quot (det_ne R.ib)).trans (matched.first ▸ h.1)
  have second : |oldForm j A B|≤L^2 := (quot (det_ne R.ia)).trans (matched.second ▸ h.2)
  have aj : det i j*A=coeffB j*oldForm i A B-coeffB i*oldForm j A B := by simp only [form_coeff,det];ring
  have bj : det i j*B=coeffA i*oldForm j A B-coeffA j*oldForm i A B := by simp only [form_coeff,det];ring
  have catalogue : ∀ m n : Fin 5,
      |coeffB m|+|coeffB n|≤2^13 ∧ |coeffA m|+|coeffA n|≤2^13 ∧ |det m n|≤2^17 := by decide
  have lin {x y a b U:ℤ} (hx:|x|≤U) (hy:|y|≤U) (nn:0≤U)
      (cap:|a|+|b|≤2^13) : |a*x-b*y|≤2^13*U := calc
    _ ≤ |a*x|+|b*y| := abs_sub _ _
    _ ≤ |a| * U+|b| * U := by rw [abs_mul,abs_mul]; gcongr
    _ = (|a|+|b|)*U := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right cap nn
  have aa : |A|≤2^13*L^2 := (quot minor).trans (aj ▸ lin first second Lzero (catalogue j i).1)
  have bb : |B|≤2^13*L^2 := (quot minor).trans (bj ▸ lin second first Lzero (catalogue i j).2.1)
  have ss : pairHeight A B≤2^47*|F|^2 := by
    apply (max_le aa bb).trans
    dsimp [L]
    rw [mul_pow,←sq_abs (det i j),←sq_abs F]
    have m := pow_le_pow_left₀ (abs_nonneg _) (catalogue i j).2.2 2
    calc
      _ ≤ (2:ℤ)^13*((2^17)^2*|F|^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have low : (0:ℝ)<(pairHeight A B:ℝ) := by
    exact_mod_cast pairHeight_pos A B (Or.inr (off 0))
  have Fpos : 0<(F.natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr Fn
  have cap : (pairHeight A B:ℝ)≤2^47*(F.natAbs:ℝ)^2 := by
    have zi : pairHeight A B≤(2:ℤ)^47*(F.natAbs:ℤ)^2 := by simpa only [Int.natCast_natAbs] using ss
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast] using
      (Int.cast_le (R:=ℝ)).mpr zi
  have logs:=Real.log_le_log low cap
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow] at logs
  have ln : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  change Real.log (pairHeight A B:ℝ)≤2*Real.log (F.natAbs:ℝ)+47
  norm_num only [Nat.cast_ofNat] at logs
  linarith only [logs,ln]

/-- A matched primitive slope satisfies the original height bound up to the full 24th-power
logarithmic budget on its center. No restriction on the center's prime support is needed. -/
theorem split_sector (R : ThreeRows) {A B d u v : ℤ} (off : ∀ i,oldForm i A B≠0)
    (matched : R.Match A B d u v)
    (center : numberLog (oldForm R.center A B) ≤ (heightRadical A B:ℝ)^24) :
    pairLogHeight A B ≤ glazerConstant24*(oddProduct A B:ℝ)^24 := by
  let T:ℝ:=heightRadical A B
  have tm : 1≤T := Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tm' : 1≤T^24 := one_le_pow₀ tm
  have upper := split_height R off matched
  have small : pairLogHeight A B ≤ 49*T^24 := by
    change numberLog (oldForm R.center A B)≤T^24 at center
    linarith only [upper,center,tm']
  have wide : (49:ℝ)≤2^810 := by
    calc
      _ ≤ 2^6 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide)
  exact (small.trans (mul_le_mul_of_nonneg_right wide (by positivity))).trans (original_margin A B)

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.split_raw
#print axioms ZInQBlueprint.SplitRows.split_height
#print axioms ZInQBlueprint.SplitRows.split_sector
