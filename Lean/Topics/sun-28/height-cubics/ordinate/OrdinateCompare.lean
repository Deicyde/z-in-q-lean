import OrdinateHeight

namespace Sun28.HeightCubics.Ordinate
open Sun28.FiveMarkUnits Sun28.HeightFibres
noncomputable section

theorem symmetric_le {N:ℕ} (np:0<N) : symmetricBound N≤estimate N := by
  have one:1≤(N:ℝ):=Nat.one_le_cast.mpr np
  have coef:1≤4*(N:ℝ)^6:=by nlinarith only [one_le_pow₀ one (n:=6)]
  have zero:=Real.log_nonneg coef
  have cost:0≤(62208*(N:ℝ)^2)*(Real.log (62208*(N:ℝ)^2))^2:=by positivity
  unfold symmetricBound estimate
  linarith only [zero,cost]

theorem mixed_le {N:ℕ} (np:0<N) : mixedBound N≤ mixedEstimate N := by
  have one:1≤(N:ℝ):=Nat.one_le_cast.mpr np
  have zero:=Real.log_nonneg one
  have cost:0≤(62208*(N:ℝ)^2)*(Real.log (62208*(N:ℝ)^2))^2:=by positivity
  unfold mixedBound mixedEstimate
  linarith only [zero,cost]

theorem covers_prior {A B:ℤ} (prior:HeightCubics.Covered A B ∨ MixedCovered A B) : Covered A B := by
  rcases prior with ⟨r,small⟩|⟨r,small⟩
  · have pos:0<chartN r A B:=Finset.prod_pos fun _ mem=>(places_prime mem).pos
    exact ⟨r,(min_le_left _ _).trans ((symmetric_le pos).trans small)⟩
  · have pos:0< mixedChart r A B:=Finset.prod_pos fun _ mem=>(mixed_prime mem).pos
    exact ⟨r,(min_le_right _ _).trans ((mixed_le pos).trans small)⟩

end
end Sun28.HeightCubics.Ordinate
#print axioms Sun28.HeightCubics.Ordinate.symmetric_le
#print axioms Sun28.HeightCubics.Ordinate.mixed_le
#print axioms Sun28.HeightCubics.Ordinate.covers_prior
