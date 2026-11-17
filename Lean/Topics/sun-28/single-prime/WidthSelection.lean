import BoxRecords
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Sqrt

namespace Sun28.SinglePrime
open Filter
noncomputable section

/-- At a fixed aspect ratio the height of the rectangle is a fixed fraction of the square root. -/
def rowWidth (j b : ℕ) : ℕ := b.sqrt / (j+1)

theorem row_grows (j m : ℕ) : ∀ᶠ b : ℕ in atTop,m≤rowWidth j b := by
  filter_upwards [eventually_ge_atTop ((m*(j+1))^2)] with b hb
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.le_sqrt'.mpr hb)

theorem row_area (j b : ℕ) : (rowWidth j b:ℝ)^2*((j:ℝ)+1)≤b := by
  have h₁ := Nat.div_le_self b.sqrt (j+1)
  have h₂ := Nat.div_mul_le_self b.sqrt (j+1)
  have h : (rowWidth j b)^2*(j+1)≤b := calc
    _ = rowWidth j b*(rowWidth j b*(j+1)) := by ring
    _ ≤ b.sqrt*b.sqrt := Nat.mul_le_mul h₁ h₂
    _ ≤ b := Nat.sqrt_le _
  exact_mod_cast h

/-- Select a growing level at which its pointwise eventual estimate holds. -/
theorem diagonal_level (P : ℕ→ℕ→Prop) (h : ∀ j,∀ᶠ b in atTop,P j b) :
    ∃ stage : ℕ→ℕ,Tendsto stage atTop atTop ∧ ∀ᶠ b in atTop,P (stage b) b := by
  classical
  let stage := fun b => Nat.findGreatest (fun j => P j b) b
  refine ⟨stage,tendsto_atTop.mpr (fun j=>?_),?_⟩
  · filter_upwards [eventually_ge_atTop j,h j] with b jb good
    exact Nat.le_findGreatest jb good
  · filter_upwards [h 0] with b good
    exact Nat.findGreatest_spec (P := fun j => P j b) (Nat.zero_le b) good

theorem eventual_error {stage : ℕ→ℕ} (g : Tendsto stage atTop atTop)
    {ε : ℝ} (pos : 0<ε) : ∀ᶠ b : ℕ in atTop,1/((stage b:ℝ)+1)≤ε := by
  obtain ⟨j,hj⟩:=exists_nat_one_div_lt pos
  filter_upwards [tendsto_atTop.mp g j] with b hb
  have h : (j:ℝ)+1 ≤(stage b:ℝ)+1 := by exact_mod_cast (Nat.succ_le_succ hb)
  exact (one_div_le_one_div_of_le (by positivity) h).trans hj.le

/-- A numerical threshold may tend to infinity arbitrarily slowly below every fixed row.
The selected widths satisfy the threshold, grow to infinity, and have square little-o of b. -/
theorem choose_width (ω : ℕ→ℕ) (P : ℕ→ℕ→Prop)
    (slow : ∀ j,∀ᶠ b : ℕ in atTop,ω b≤rowWidth j b)
    (rows : ∀ j,∀ᶠ b : ℕ in atTop,P j b) :
    ∃ stage : ℕ→ℕ,Tendsto stage atTop atTop ∧
      (∀ᶠ b in atTop,P (stage b) b ∧ ω b≤rowWidth (stage b) b) ∧
      Tendsto (fun b=>rowWidth (stage b) b) atTop atTop ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ b : ℕ in atTop,(rowWidth (stage b) b:ℝ)^2≤ε*b := by
  obtain ⟨s,up,good⟩:=diagonal_level (fun j b=> (P j b ∧ ω b≤rowWidth j b) ∧ j≤rowWidth j b)
    fun j=>((rows j).and (slow j)).and (row_grows j j)
  refine ⟨s,up,good.mono (fun b h=>h.1),tendsto_atTop.mpr (fun j=>?_),?_⟩
  · filter_upwards [tendsto_atTop.mp up j,good] with b hj hb
    exact hj.trans hb.2
  · intro ε ep
    filter_upwards [eventual_error up ep] with b hb
    have q : 0<(s b:ℝ)+1 := by positivity
    have r := (le_div_iff₀ q).mpr (row_area (s b) b)
    calc
      (rowWidth (s b) b:ℝ)^2≤(b:ℝ)/((s b:ℝ)+1) := r
      _ = 1/((s b:ℝ)+1)*b := by ring
      _ ≤ ε*b := mul_le_mul_of_nonneg_right hb (by positivity)

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.row_grows
#print axioms Sun28.SinglePrime.row_area
#print axioms Sun28.SinglePrime.diagonal_level
#print axioms Sun28.SinglePrime.eventual_error
#print axioms Sun28.SinglePrime.choose_width
