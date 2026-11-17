import EmbeddedBranches

/-! Matching the rational sextic to its local split integral chart at a prescribed embedding. -/
open Polynomial
namespace ZInQBlueprint.BranchPlaces
open BranchDepth BranchHeight ContactInvariant ClusterRoots ClusterPicture ResidueExtension PrimitiveParameters
open DirectCharts IntegralSextic SexticThetaHeight
noncomputable section

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

/-- The chart parameter in the common target is exactly t or 27/t, according to the two
integral coordinate descriptions. This uses only the canonical homogeneous numerator and denominator. -/
theorem parameter_chart {Ω : Type*} [Field Ω] [CharZero Ω] (φ : W →+* Ω)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) {t v a : Zp} (hc : Coordinates p u t v a) :
    φ (fromPadics p t)=(SexticIgusaChart.parameter u:Ω) ∨
    φ (fromPadics p t)=27/(SexticIgusaChart.parameter u:Ω) := by
  let q := φ.comp (fromPadics p)
  have hL : q (left p u)=(SexticIgusaChart.left u:Ω) := by
    simp [q,left,SexticIgusaChart.left,m]
    simp only [map_ofNat]
  have hR : q (right p u)=(SexticIgusaChart.right u:Ω) := by
    simp [q,right,SexticIgusaChart.right,n]
    simp only [map_ofNat]
  obtain ⟨hL',hR',_⟩ := SexticIgusaChart.parameters hu
  have hL₀ : (SexticIgusaChart.left u:Ω)≠0 := by exact_mod_cast hL'
  have hR₀ : (SexticIgusaChart.right u:Ω)≠0 := by exact_mod_cast hR'
  cases hc with
  | first _ h ht =>
    left
    have he := congrArg q ht
    rw [map_mul,h,hL,hR] at he
    change q t=_
    simp only [SexticIgusaChart.parameter,Rat.cast_div]
    exact (eq_div_iff hL₀).mpr (by simpa [mul_comm] using he)
  | second _ h ht =>
    right
    have he := congrArg q ht
    rw [map_mul,h,hR,map_mul,map_ofNat,hL] at he
    change q t=_
    rw [SexticIgusaChart.parameter,Rat.cast_div,div_div_eq_mul_div]
    exact (eq_div_iff hR₀).mpr (by simpa [mul_comm] using he)

private theorem rational_root {Ω : Type*} [Field Ω] [CharZero Ω] {u δ : ℚ}
    (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0) {z : Ω} (hz : aeval z (sextic u δ)=0) :
    form 1 (SexticIgusaChart.parameter u:Ω) z 1=0 := by
  have hscalar : (SexticIgusaChart.scalar u δ:Ω)≠0 := by exact_mod_cast (SexticIgusaChart.unmarked hu hδ).2.1
  simp [sextic,monicSextic,form,alpha,beta,gamma,hscalar] at hz ⊢
  convert hz using 1
  simp only [map_ofNat]

private theorem reciprocal_root {Ω : Type*} [Field Ω] [CharZero Ω] {s z : Ω} (hs : s≠0)
    (hz : form 1 s z 1=0) : z≠0 ∧ form 1 (27/s) (6/z) 1=0 := by
  have hn : z≠0 := by
    rintro rfl
    simp [form,alpha,beta,gamma,hs] at hz
  refine ⟨hn,?_⟩
  have he : z^6*s^2*form 1 (27/s) (6/z) 1 = 5832*form 1 s z 1 := by
    unfold form alpha beta gamma
    field_simp [hn,hs]
    ring
  rw [hz,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (pow_ne_zero _ hn) (pow_ne_zero _ hs))

private theorem label_roots {Ω : Type*} [Field Ω] (φ : W →+* Ω) (hφ : Function.Injective φ)
    {t c : W} (T : SexticFibre (monicSextic t) c)
    {z : Fin 6 → Ω} (hi : Function.Injective z) (hz : ∀ i, form 1 (φ t) (z i) 1=0) :
    ∃ e : Fin 6 ≃ Index, ∀ i, z i=φ (point T (e i)) := by
  classical
  have ex (i) : ∃ j : Index, z i=φ (point T j) := by
    have hr : ((monicSextic t).map φ).IsRoot (z i) := by
      simpa [Polynomial.IsRoot,monicSextic,form,alpha,beta,gamma] using hz i
    obtain ⟨j,k,h⟩ := (ClusterRoots.root_iff T φ hφ (z i)).mp hr
    exact ⟨(j,k),h⟩
  choose e he using ex
  have hei : Function.Injective e := by
    intro i k hik
    exact hi ((he i).trans ((congrArg (fun j => φ (point T j)) hik).trans (he k).symm))
  exact ⟨Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hei,by decide⟩),he⟩

/-- At each prescribed embedding of the intrinsic coordinate field, the actual normalized
weights equal those of a labeling of the same local Hensel fibre, in either coordinate chart. -/
theorem at_chart {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (σ : weightField r →+* Ω) (φ : W →+* Ω) (hφ : Function.Injective φ)
    {t v a : Zp} (hc : Coordinates p u t v a) {c : W}
    (T : SexticFibre (monicSextic (fromPadics p t)) c) :
    ∃ e : Fin 6 ≃ Index, ∀ i, σ (sumWeights r i) = normalizedFibre p φ T e i := by
  obtain ⟨z,hi,hroot,hw⟩ := embedded_branches hu hδ hr hz σ
  have hform (i) := rational_root hu hδ (hroot i)
  have ht := parameter_chart p φ hu hc
  have transfer {y : Fin 6 → Ω} (hy : Function.Injective y)
      (hyroot : ∀ j, form 1 (φ (fromPadics p t)) (y j) 1=0)
      (hweight : ∀ i, normalized (weight y) i=normalized (weight z) i) :
      ∃ e : Fin 6 ≃ Index, ∀ i, σ (sumWeights r i) = normalizedFibre p φ T e i := by
    obtain ⟨e,he⟩ := label_roots p φ hφ T hy hyroot
    refine ⟨e,fun i => (hw i).trans ((hweight i).symm.trans ?_)⟩
    rw [show y = (fun j => φ (point T (e j))) from funext he]
    simp only [normalizedFibre,map_weight]
  rcases ht with ht|ht
  · exact transfer hi (fun j => ht ▸ hform j) (fun _ => rfl)
  · have hs : (SexticIgusaChart.parameter u:Ω)≠0 := by exact_mod_cast (SexticIgusaChart.unmarked hu hδ).1
    have recip (i) := reciprocal_root hs (hform i)
    have h6 : (6:Ω) ≠ 0 := by norm_num
    have hy : Function.Injective (fun j => 6/z j) := by
      intro i k he
      apply hi
      change 6 / z i = 6 / z k at he
      simp only [div_eq_mul_inv] at he
      exact inv_injective (mul_left_cancel₀ h6 he)
    apply transfer hy
    · intro j
      rw [ht]
      exact (recip j).2
    · intro i
      simpa [mobius] using normalized_mobius z 0 6 1 0 (by norm_num) (fun j => by simpa using (recip j).1) i

end
end ZInQBlueprint.BranchPlaces
#print axioms ZInQBlueprint.BranchPlaces.parameter_chart
#print axioms ZInQBlueprint.BranchPlaces.at_chart
