import InteriorTransfer

namespace Sun28.PrimeTransfer
open Filter Topology
noncomputable section

/-- Freezing a modulus at a fixed error: it is enough to find one accurate
diagonal value on any cofinal diagonal for which the scale has been made
arbitrarily large relative to its modulus and chosen row. -/
theorem freeze_modulus (P : ℕ→ℕ→ℕ→Prop)
    (along : ∃ H : ℕ→ℕ, ∀ j : ℕ→ℕ, ∀ T : ℕ→ℕ, Tendsto T atTop atTop →
      (∀ w,H w ≤ T w) → (∀ w,j w ≤ T w) → ∃ w,P w (j w) (T w)) :
    ∃ w,∀ j,∀ᶠ t : ℕ in atTop,P w j t := by
  classical
  obtain ⟨H,h⟩:=along
  by_contra! no
  have wi (w : ℕ) : ∃ j, ∀ a,∃ t≥a,¬P w j t := by
    obtain ⟨j,hj⟩:=no w
    exact ⟨j,frequently_atTop.mp hj⟩
  choose j bad using wi
  choose T hT fail using fun w => bad w (max w (max (H w) (j w)))
  have grows : Tendsto T atTop atTop := tendsto_atTop.mpr (fun b => (eventually_ge_atTop b).mono
    (fun w hw => hw.trans ((le_max_left ..).trans (hT w))))
  obtain ⟨w,ok⟩ := h j T grows (fun w=>(le_max_left ..).trans ((le_max_right ..).trans (hT w)))
    (fun w=>(le_max_right ..).trans ((le_max_right ..).trans (hT w)))
  exact fail w ok

/-- The required family of moduli may be restricted to primorials. To conclude
at some positive V no estimate is needed at V=0. -/
theorem freeze_in_family (P : ℕ→ℕ→ℕ→Prop) (V : ℕ→ℕ) (vp : ∀ w,0<V w)
    (along : ∃ H : ℕ→ℕ, ∀ j : ℕ→ℕ, ∀ T : ℕ→ℕ, Tendsto T atTop atTop →
      (∀ w,H w ≤ T w) → (∀ w,j w ≤ T w) → ∃ w,P (V w) (j w) (T w)) :
    ∃ v,0<v ∧ ∀j,∀ᶠ t : ℕ in atTop,P v j t := by
  obtain ⟨w,h⟩:=freeze_modulus (fun w=>P (V w)) along
  exact ⟨V w,vp w,h⟩

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.freeze_modulus
#print axioms Sun28.PrimeTransfer.freeze_in_family
