import ConeApplication
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace Sun28.ConeReal
open Sun28.QuadricSieve Set Metric
open scoped ContDiff
noncomputable section

def rad (z : ℝ × ℝ) := z.1^2 + z.2^2
def form (κ : ℝ) (x : Coordinates ℝ) := rad x.1 - rad x.2.1 - κ*x.2.2^2
def width (j : ℕ) : ℝ := ((j:ℝ)+1)⁻¹
theorem width_pos (j : ℕ) : 0 < width j := by unfold width; positivity
theorem width_le (j : ℕ) : width j ≤ 1 := by
  unfold width; rw [inv_le_one₀ (by positivity)]; have := Nat.cast_nonneg (α:=ℝ) j; linarith

def radial : ContDiffBump (3/4:ℝ) := ⟨1/2,5/8,by norm_num,by norm_num⟩
def axial : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def weight (j : ℕ) (x : Coordinates ℝ) :=
  radial (rad x.1) * radial (rad x.2.1) * axial (((j:ℝ)+1)*x.2.2)

theorem weight_bounds (j : ℕ) (x : Coordinates ℝ) : 0 ≤ weight j x ∧ weight j x ≤ 1 := by
  unfold weight
  exact ⟨mul_nonneg (mul_nonneg radial.nonneg radial.nonneg) axial.nonneg,
    by calc _ ≤ 1 * 1 * (1:ℝ) := by gcongr <;> first | exact radial.le_one | exact axial.le_one | exact radial.nonneg | exact axial.nonneg
       _ = 1 := by norm_num⟩

theorem smooth_weight (j : ℕ) : ContDiff ℝ ∞ (weight j) := by
  unfold weight
  exact ((radial.contDiff.comp (by unfold rad;fun_prop)).mul
    (radial.contDiff.comp (by unfold rad;fun_prop))).mul (axial.contDiff.comp (by fun_prop))

theorem plateau (j : ℕ) (x : Coordinates ℝ) (h₁ : rad x.1 ∈ Icc (1/4:ℝ) (5/4))
    (h₂ : rad x.2.1 ∈ Icc (1/4:ℝ) (5/4)) (hv : |x.2.2| ≤ width j) : weight j x = 1 := by
  have r (s : ℝ) (h : s ∈ Icc (1/4:ℝ) (5/4)) : radial s=1 := by
    apply radial.one_of_mem_closedBall
    change dist s (3/4) ≤ 1/2
    rw [Real.dist_eq,abs_le];constructor <;> linarith [h.1,h.2]
  have a : axial (((j:ℝ)+1)*x.2.2)=1 := by
    apply axial.one_of_mem_closedBall
    change dist _ 0 ≤ 1
    rw [Real.dist_eq,sub_zero,abs_mul,abs_of_pos (by positivity : 0<(j:ℝ)+1)]
    change |x.2.2|≤((j:ℝ)+1)⁻¹ at hv
    calc _ ≤ ((j:ℝ)+1)*((j:ℝ)+1)⁻¹ := by gcongr
         _ = 1 := mul_inv_cancel₀ (by positivity)
  simp only [weight,r _ h₁,r _ h₂,a,mul_one]

/-- Bounds on the closed support, including its boundary. -/
theorem support_bounds (j : ℕ) {x : Coordinates ℝ} (hx : x∈tsupport (weight j)) :
    rad x.1 ∈ Icc (1/8:ℝ) (11/8) ∧ rad x.2.1 ∈ Icc (1/8:ℝ) (11/8) ∧ |x.2.2|≤2*width j := by
  let K : Set (Coordinates ℝ) := {y | rad y.1 ∈ Icc (1/8:ℝ) (11/8) ∧ rad y.2.1 ∈ Icc (1/8:ℝ) (11/8) ∧ |y.2.2| ≤ 2*width j}
  have closed : IsClosed K := by
    change IsClosed ((fun y : Coordinates ℝ=>rad y.1) ⁻¹' Icc _ _ ∩
      ((fun y : Coordinates ℝ=>rad y.2.1) ⁻¹' Icc _ _ ∩ (fun y : Coordinates ℝ => |y.2.2|) ⁻¹' Iic _))
    exact (isClosed_Icc.preimage (by unfold rad;fun_prop)).inter
      ((isClosed_Icc.preimage (by unfold rad;fun_prop)).inter (isClosed_Iic.preimage (by fun_prop)))
  apply (closure_minimal (t:=K) ?_ closed) hx
  intro y hy
  change radial (rad y.1)*radial (rad y.2.1)*axial (((j:ℝ)+1)*y.2.2)≠0 at hy
  have h:=mul_ne_zero_iff.mp hy
  have r (s : ℝ) (hs : radial s≠0) : s ∈ Icc (1/8:ℝ) (11/8) := by
    have h' : s∈Function.support radial := hs
    rw [radial.support_eq,Metric.mem_ball,Real.dist_eq] at h'
    have b:=abs_lt.mp (show |s-3/4|<5/8 from h')
    exact ⟨by linarith [b.1],by linarith [b.2]⟩
  refine ⟨r _ (mul_ne_zero_iff.mp h.1).1,r _ (mul_ne_zero_iff.mp h.1).2,?_⟩
  have h' : ((j:ℝ)+1)*y.2.2 ∈ Function.support axial := h.2
  rw [axial.support_eq,Metric.mem_ball,Real.dist_eq,sub_zero,abs_mul,abs_of_pos (by positivity : 0<(j:ℝ)+1)] at h'
  change ((j:ℝ)+1)*|y.2.2|<2 at h'
  rw [width,←div_eq_mul_inv,le_div_iff₀ (by positivity : 0<(j:ℝ)+1)]
  linarith

theorem support_norm (j : ℕ) {x : Coordinates ℝ} (hx : x∈tsupport (weight j)) : ‖x‖≤2 := by
  obtain ⟨h₁,h₂,hv⟩:=support_bounds j hx
  have axis (z : ℝ×ℝ) (h:rad z≤11/8) : ‖z‖≤2 := by
    unfold rad at h
    simp only [Prod.norm_def,sup_le_iff,Real.norm_eq_abs,abs_le]
    constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]
  rw [Prod.norm_def,sup_le_iff]
  refine ⟨axis _ h₁.2,?_⟩
  rw [Prod.norm_def,sup_le_iff,Real.norm_eq_abs]
  exact ⟨axis _ h₂.2,hv.trans (by linarith [width_le j])⟩

theorem compact_weight (j : ℕ) : HasCompactSupport (weight j) := by
  apply (isCompact_closedBall (0:Coordinates ℝ) 2).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  simpa [Metric.mem_closedBall] using support_norm j hx

def gradSq (κ : ℝ) (x : Coordinates ℝ) :=
  (2*x.1.1)^2+(2*x.1.2)^2+(-2*x.2.1.1)^2+(-2*x.2.1.2)^2+(-2*κ*x.2.2)^2

theorem regular_support (κ : ℝ) (j : ℕ) {x : Coordinates ℝ} (hx : x∈tsupport (weight j)) :
    (1:ℝ)≤gradSq κ x := by
  obtain ⟨h₁,h₂,_⟩:=support_bounds j hx
  have a:=h₁.1;have b:=h₂.1
  dsimp [rad] at a b
  dsimp [gradSq];nlinarith only [a,b,sq_nonneg (-2*κ*x.2.2)]

end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.smooth_weight
#print axioms Sun28.ConeReal.support_bounds
#print axioms Sun28.ConeReal.compact_weight
#print axioms Sun28.ConeReal.regular_support
