import FreezeModulus

namespace Sun28.PrimeTransfer
open Filter Topology
noncomputable section

/-- A row-dependent threshold is permitted. This is the useful form when the
inner width is divided by j+1 before invoking a local norm theorem. -/
theorem freeze_with_row_threshold (P : ℕ→ℕ→ℕ→Prop) (V : ℕ→ℕ) (vp : ∀ w,0<V w)
    (along : ∃ H : ℕ→ℕ→ℕ, ∀ j : ℕ→ℕ, ∀ T : ℕ→ℕ, Tendsto T atTop atTop →
      (∀ w,H w (j w) ≤ T w) → ∃ w,P (V w) (j w) (T w)) :
    ∃ v,0<v ∧ ∀j,∀ᶠ t : ℕ in atTop,P v j t := by
  classical
  obtain ⟨H,h⟩:=along
  by_contra! fail
  have wi (w : ℕ) : ∃ j,∀ a,∃ t≥a,¬P (V w) j t := by
    obtain ⟨j,hj⟩:=fail (V w) (vp w)
    exact ⟨j,frequently_atTop.mp hj⟩
  choose j bad using wi
  choose T a b using fun w=>bad w (max w (H w (j w)))
  have grows : Tendsto T atTop atTop := tendsto_atTop.mpr fun u =>
    (eventually_ge_atTop u).mono (fun w hw=>hw.trans ((le_max_left ..).trans (a w)))
  obtain ⟨w,ok⟩:=h j T grows (fun w=>(le_max_right ..).trans (a w))
  exact b w ok

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.freeze_with_row_threshold
