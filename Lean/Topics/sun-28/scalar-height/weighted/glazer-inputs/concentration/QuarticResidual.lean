import QuarticPoints

namespace ZInQBlueprint.OriginalConcentrated
open scoped Classical
open Finset Height Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres ZInQBlueprint.OriginalHeightCount
noncomputable section
set_option maxRecDepth 12000
attribute [local irreducible] glazerConstant24

/-- Signed smooth twists whose computed Mordell--Weil ranks are positive, indexed by the omitted form. -/
def positiveTwists : Fin 5→Finset ℤ :=
 ![{1,2,15,30,35,70,210,-5,-7,-10,-21,-30,-35,-42,-70},
   {1,7,14,35,70,105,210,-3,-6,-7,-30},
   {1,2,6,10,14,21,30,70,-2,-3,-10,-21,-35,-105},
   {6,10,14,15,35,42,-2,-5,-6,-7,-14,-21,-35,-210},
   {2,6,10,15,30,35,42,210,-5,-6,-7,-21,-30,-35}]

/-- Union of the off-mark slopes on the 92 endpoint cubics classified as rank zero. -/
def finiteSlopes : Finset ℚ :=
 {-749,-49,77/2,1127/2,-343/2,2401/16,-21/4,-7/8,49/24,49/4,49}

/-- Scope of the external rank/torsion calculation on the 92 explicit rank-zero twists. -/
def FiniteCatalogue : Prop :=
 ∀ (j:Fin 5) (d:ℤ), d.natAbs∣210 → d∉positiveTwists j → ∀ x:ℚ,
     offMarks x → OnTwist j x d → x∈finiteSlopes

theorem finite_height {x:ℚ} (mem:x∈finiteSlopes) : ¬failure x := by
  have bound : ∀ z∈finiteSlopes, max z.num.natAbs z.den≤2401 := by
    intro z hz
    simp only [finiteSlopes,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  have realBound : ((max x.num.natAbs x.den:ℕ):ℝ)≤2401 := by exact_mod_cast bound x mem
  have h : logHeight₁ x≤2401 := by
    rw [Rat.logHeight₁_eq_log_max]
    exact (Real.log_le_self (by positivity)).trans realBound
  let T := heightRadical x.num x.den
  have pos : (1:ℝ)≤T := Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd x.num x.den))
  have big : (2401:ℝ)≤2^810 := (by norm_num : (2401:ℝ)≤2^12).trans (pow_le_pow_right₀ (by norm_num) (by decide))
  have weak : (2401:ℝ)≤2^810*(T:ℝ)^24 :=
    big.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ pos))
  intro err
  exact (not_lt_of_ge (h.trans (weak.trans (original_margin x.num x.den)))) err.2

theorem remaining_twists (complete:FiniteCatalogue) {x:ℚ} (err:failure x) (j:Fin 5)
    (single:Concentrated x j) : signedTwist j x∈positiveTwists j ∧ OnTwist j x (signedTwist j x) := by
  have hit:=point_on_twist err.1 j
  refine ⟨?_,hit⟩
  by_contra no
  exact finite_height (complete j _ ((concentrated_iff_twist err.1 j).mp single) no x err.1 hit) err

/-- Reduction of the concentrated part of the original universal estimate to the 68 cubics. -/
theorem concentrated_height_iff (complete:FiniteCatalogue) :
    (∀ x j, Concentrated x j → ¬failure x) ↔
    (∀ j d, d∈positiveTwists j → ∀ x:ℚ, offMarks x → OnTwist j x d → ¬failure x) := by
  constructor
  · intro all j d hd x hx point
    have smooth : ∀ j:Fin 5,∀ d∈positiveTwists j,d.natAbs∣210 := by decide
    exact all x j ((concentrated_iff_cubic hx j).mpr ⟨d,smooth j d hd,point⟩)
  · intro residual x j concentrated err
    have h:=remaining_twists complete err j concentrated
    exact residual j _ h.1 x err.1 h.2 err

end
end ZInQBlueprint.OriginalConcentrated
#print axioms ZInQBlueprint.OriginalConcentrated.finite_height
#print axioms ZInQBlueprint.OriginalConcentrated.remaining_twists
#print axioms ZInQBlueprint.OriginalConcentrated.concentrated_height_iff

