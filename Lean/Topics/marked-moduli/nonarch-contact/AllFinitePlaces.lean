import NonarchCharts
import CompletedBranchPlaces

/-! An unconditional denominator bound at every finite place of the intrinsic field. -/
open Polynomial NumberField
namespace ZInQBlueprint.NonarchContact
open BranchDepth BranchHeight ContactInvariant BranchPlaces DirectCharts IntegralSextic
open ResidualFactors CurveChart SexticThetaHeight
noncomputable section

private theorem paper_chart {L : Type*} [NormedField L] [IsUltrametricDist L] [CharZero L]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    (r : Fin 6 → L) (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (i : Fin 10) : ‖normalized (weight r) i‖ * ‖(denominator u:L)‖ ≤ 1 := by
  let m₀ := m u.num (u.den:ℤ)
  let n₀ := n u.num (u.den:ℤ)
  let G := poleForm u.num (u.den:ℤ)
  have hm : (m₀:L)=(SexticIgusaChart.left u : L) := by
    simp [m₀,SexticIgusaChart.left,m]
  have hn : (n₀:L)=(SexticIgusaChart.right u : L) := by
    simp [n₀,SexticIgusaChart.right,n]
  obtain ⟨hm',hn',_⟩ := SexticIgusaChart.parameters hu
  have hm₀ : (m₀:L) ≠ 0 := hm ▸ (by exact_mod_cast hm')
  have hn₀ : (n₀:L) ≠ 0 := hn ▸ (by exact_mod_cast hn')
  have hG : (G:L) ≠ 0 := by exact_mod_cast (pole_positive u).ne'
  have hid : (G:L)^3 = 27*(m₀:L)^2+(n₀:L)^2 := by
    exact_mod_cast (parameter_identities u.num (u.den:ℤ)).2.1
  have hs : (SexticIgusaChart.scalar u δ : L) ≠ 0 := by exact_mod_cast (SexticIgusaChart.unmarked hu hδ).2.1
  have he (j) : form 1 ((n₀:L)/(m₀:L)) (r j) 1=0 := by
    rw [hn,hm,show ((SexticIgusaChart.right u:L)/(SexticIgusaChart.left u:L)) =
        (SexticIgusaChart.parameter u:L) from (Rat.cast_div ..).symm]
    have h := hz j
    simp [sextic,monicSextic,form,alpha,beta,gamma,hs] at h ⊢
    simpa only [map_ofNat] using h
  have hd : (denominator u:L) = 144*(3:L)^4*27^2*(G:L)^6 := by
    exact_mod_cast denominator_pole u
  rw [hd]
  exact homogeneous_bound hm₀ hn₀ hG (IsUltrametricDist.norm_intCast_le_one L m₀)
    (IsUltrametricDist.norm_intCast_le_one L n₀) hid r hr he i

/-- Every sum-normalized branch coordinate has denominator dividing D at each finite place,
including the places above 2 and 3 and contacts of odd order. -/
theorem finite_place_bound {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0) :
    letI := weight_numberField hu hδ hz
    ∀ (w : FinitePlace (weightField r)) (i : Fin 10),
      w (sumWeights r i) ≤ (w (denominator u:weightField r))⁻¹ := by
  let := weight_numberField hu hδ hz
  intro w i
  let K := weightField r
  let E := w.maximalIdeal.adicCompletion K
  let Ω := AlgebraicClosure E
  let : NontriviallyNormedField E := Valued.toNontriviallyNormedField E (WithZero (Multiplicative ℤ))
  let : IsUltrametricDist E := inferInstanceAs (IsUltrametricDist (w.maximalIdeal.adicCompletion K))
  let : NormedField Ω := spectralNorm.normedField E Ω
  let : IsUltrametricDist Ω := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K:=E) (L:=Ω))
  let σ := (algebraMap E Ω).comp (FinitePlace.embedding (K:=K) w.maximalIdeal)
  let : CharZero Ω := (RingHom.charZero_iff σ.injective).mp inferInstance
  have hn (x : K) : ‖σ x‖=w x := by
    change spectralNorm E Ω (algebraMap E Ω (FinitePlace.embedding w.maximalIdeal x)) = w x
    rw [spectralNorm_extends,FinitePlace.norm_embedding_eq]
  obtain ⟨z,hz₁,hz₂,hz₃⟩ := embedded_branches hu hδ hr hz σ
  have hd : 0 < w (denominator u:K) := FinitePlace.pos_iff.mpr (Nat.cast_ne_zero.mpr (denominator_pos u).ne')
  rw [← one_div,le_div_iff₀ hd,← hn,← hn,hz₃,map_natCast]
  exact paper_chart hu hδ z hz₁ hz₂ i

/-- Integral coordinates summing to one have supremum one. This applies at every
finite place where the explicit clearing denominator has absolute value one. -/
theorem supremum_of_unit {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0) :
    letI := weight_numberField hu hδ hz
    ∀ w : FinitePlace (weightField r), w (denominator u:weightField r)=1 →
      (⨆ i : Fin 10, w (sumWeights r i))=1 := by
  let := weight_numberField hu hδ hz
  intro w hw
  have hi (i : Fin 10) : w (sumWeights r i) ≤ 1 := by
    simpa only [hw,inv_one] using finite_place_bound hu hδ hr hz w i
  apply le_antisymm (ciSup_le hi)
  have hna : IsNonarchimedean (fun x : weightField r => w x) := fun x y => w.add_le x y
  obtain ⟨j,_,hj⟩ := hna.finset_image_add_of_nonempty (g:=sumWeights r) Finset.univ_nonempty
  rw [(sumWeights_equations hu hδ hr hz).1,map_one] at hj
  exact hj.trans (le_ciSup (Finite.bddAbove_range (fun k : Fin 10 => w (sumWeights r k))) j)

end
end ZInQBlueprint.NonarchContact
#print axioms ZInQBlueprint.NonarchContact.finite_place_bound
#print axioms ZInQBlueprint.NonarchContact.supremum_of_unit
