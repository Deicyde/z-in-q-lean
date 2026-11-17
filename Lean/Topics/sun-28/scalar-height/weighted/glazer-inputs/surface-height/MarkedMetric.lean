import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A nearest marked point controls the curvature expression at all complex arguments. -/
namespace ZInQBlueprint.FiveMetric
open Finset
noncomputable section

def mark (i : Fin 4) : ℂ := ![0,32,76832,-343] i

def radius (z : ℂ) (i : Fin 4) := ‖z-mark i‖
def mass (z : ℂ) := 65536+∑ i,radius z i
def triples (z : ℂ) := ∑ i : Fin 4, ∏ j∈univ.erase i,radius z j

private def factor (i j : Fin 4) : ℕ :=
  ![![1,8926,8,837],![8926,1,8,766],![12,12,1,12],![841,769,8,1]] i j

private theorem table {i j : Fin 4} (ne:i≠j) :
    4≤(factor i j:ℝ) ∧
    2*(65536+∑ k : Fin 4, ‖mark i-mark k‖)≤((factor i j:ℝ)-4)*‖mark i-mark j‖ := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_four,mark,factor,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at *

private theorem nearest_ratio (z : ℂ) (i j : Fin 4) (ne:j≠i) (near:radius z i≤radius z j) :
    mass z≤(factor i j:ℝ)*radius z j := by
  have h : ∀ k,radius z k ≤ radius z i+‖mark i-mark k‖ := by
    intro k
    simpa only [sub_add_sub_cancel,radius] using norm_add_le (z-mark i) (mark i-mark k)
  have up:=sum_le_sum (s:=univ) (fun k _=>h k)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at up
  have dist:=norm_add_le (mark i-z) (z-mark j)
  rw [sub_add_sub_cancel,norm_sub_rev (mark i) z] at dist
  change _≤radius z i+radius z j at dist
  obtain ⟨f,comp⟩:=table ne.symm
  have cover:=mul_le_mul_of_nonneg_left (dist.trans (show radius z i+radius z j≤2*radius z j by linarith))
    (sub_nonneg.mpr f)
  unfold mass
  linarith only [up,comp,cover,near]

/-- The row records the four explicit distance bounds after choosing a nearest mark. -/
theorem nearest_bound (z : ℂ) :
    ∃ i : Fin 4, ∀ j≠i, mass z≤(factor i j:ℝ)*radius z j := by
  obtain ⟨i,_,near⟩:=univ.exists_min_image (radius z) univ_nonempty
  exact ⟨i,fun j ne=>nearest_ratio z i j ne (near j (mem_univ j))⟩

private theorem row_product : ∀ i : Fin 4, (∏ j∈univ.erase i,factor i j)≤67108864 := by decide

/-- The sum of the four triple products gives a uniform curvature bound. -/
theorem curvature_bound (z : ℂ) : 2*(mass z)^3≤2048*65536*triples z := by
  classical
  obtain ⟨i,large⟩:=nearest_bound z
  have small : 0≤mass z := by unfold mass radius; positivity
  have product := prod_le_prod₀ (s:=univ.erase i) (f:=fun _ : Fin 4=>mass z)
    (g:=fun j=>(factor i j:ℝ)*radius z j) (fun _ _=>small)
    (fun j hj=>large j (mem_erase.mp hj).1)
  have card : (univ.erase i).card=3 := by simp
  rw [prod_const,card,prod_mul_distrib] at product
  have row : (∏ j∈univ.erase i,(factor i j:ℝ))≤67108864 := by exact_mod_cast row_product i
  have rpos : 0≤∏ j∈univ.erase i,radius z j := prod_nonneg fun j _=>norm_nonneg _
  have one := single_le_sum (s:=univ) (f:=fun a : Fin 4=>∏ j∈univ.erase a,radius z j)
    (fun a _=>prod_nonneg fun j _=>norm_nonneg _) (mem_univ i)
  change _≤triples z at one
  linarith only [product,mul_le_mul_of_nonneg_right row rpos,
    mul_le_mul_of_nonneg_left one (by norm_num : (0:ℝ)≤67108864)]

/-- Off the four marks, assume the gradient has squared length at most 16.
Cauchy--Schwarz gives the curvature numerator for the chosen metric. -/
theorem curvature_numerator (z : ℂ) (off : ∀ i,0<radius z i) {G : ℝ} (grad : G≤16) :
    65536*triples z ≤ (mass z*(∑ i : Fin 4,1/radius z i)-G)*(∏ i : Fin 4,radius z i) := by
  classical
  let r:=radius z
  have pos : 0<∑ i : Fin 4,r i := sum_pos (fun i _=>off i) univ_nonempty
  have C:=sq_sum_div_le_sum_sq_div univ (fun _ : Fin 4=>(1:ℝ)) (g:=r) (fun i _=>off i)
  norm_num only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one,one_pow,
    Nat.reducePow,one_div] at C
  have H:= (div_le_iff₀ pos).mp C
  have loss : 65536*(∑ i : Fin 4,(r i)⁻¹) ≤ mass z*(∑ i : Fin 4,(r i)⁻¹)-G := by
    change _ ≤ (65536+∑ i : Fin 4,r i)*(∑ i : Fin 4,(r i)⁻¹)-G
    linarith only [H,grad]
  have P:=mul_le_mul_of_nonneg_right loss
    (prod_nonneg (s:=univ) (f:=r) (fun i _=>(off i).le))
  have id : (∑ i : Fin 4,(r i)⁻¹)*(∏ i : Fin 4,r i)=triples z := by
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    rw [←prod_erase_mul _ _ (mem_univ i)]
    change (r i)⁻¹*((∏ j∈univ.erase i,r j)*r i)=_
    have rn : r i ≠ 0 := (off i).ne'
    rw [mul_comm (∏ j∈univ.erase i,r j),←mul_assoc,inv_mul_cancel₀ rn,one_mul]
  rw [mul_assoc, id] at P
  simpa only [one_div] using P

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.nearest_bound
#print axioms ZInQBlueprint.FiveMetric.curvature_bound
#print axioms ZInQBlueprint.FiveMetric.curvature_numerator
