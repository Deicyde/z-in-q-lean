import PoleParameters

/-! An elementary two-sided estimate for the actual five-factor detector. -/
namespace Sun28.RealPoleBounds
open Sun28.Ordinary

theorem detector_window {A t : ℚ} (ap : 0<A) (big : 7≤t) :
    0<detector A t ∧ 1/A^5 ≤ detector A t*(t-3) ∧ detector A t*(t-3) ≤ 32/A^5 := by
  have U : 0<t-3 := by linarith
  have f (θ : ℚ) (mem : θ∈marks) : 1 ≤ (t-θ)/(t-3) ∧ (t-θ)/(t-3) ≤ 2 := by
    have bounds : -1≤θ ∧ θ≤1 := by
      norm_num [marks] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl <;> norm_num
    constructor
    · apply (le_div_iff₀ U).2;linarith
    · apply (div_le_iff₀ U).2;linarith
  let prod := ∏ θ ∈ marks, (t-θ)/(t-3)
  have one : 1≤prod := Finset.one_le_prod₀ (fun θ hm=>(f _ hm).1)
  have upper : prod ≤ 32 := by
    calc
      prod ≤ ∏ _θ ∈ marks,(2:ℚ) := Finset.prod_le_prod₀ (fun θ hm=>(zero_le_one.trans (f _ hm).1)) (fun θ hm=>(f _ hm).2)
      _ = 32 := by norm_num [marks]
  have form : detector A t*(t-3)=prod/A^5 := by
    have count : marks.card=5 := by norm_num [marks]
    dsimp [prod,detector,fiveProduct]
    rw [Finset.prod_div_distrib,Finset.prod_const,count]
    field_simp
  have pp := div_pos (zero_lt_one.trans_le one) (pow_pos ap 5)
  refine ⟨pos_of_mul_pos_left (form ▸ pp) U.le,?_,?_⟩
  · rw [form];gcongr
  · rw [form];gcongr

/-- Maximum loss from the order k across the fixed sixteen entries. -/
noncomputable def loss (A : ℝ) := max 1 ((A^5)^64)

/-- A finite threshold in u=t-3. Above it every factor is at most 2
and the pole argument is less than the prescribed positive epsilon. -/
noncomputable def depthThreshold (A C ε : ℝ) :=
  max 4 (max (C*loss A) ((32/A^5)*(max 1 ((2:ℝ)^32/ε))))

theorem order_le (i : OrdinaryTest) : orderRequired i≤64 := by cases i <;> norm_num [orderRequired]

end Sun28.RealPoleBounds
#print axioms Sun28.RealPoleBounds.detector_window
#print axioms Sun28.RealPoleBounds.order_le
