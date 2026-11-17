import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

/-! Progression recurrence inside a compact monothetic group. -/
namespace Sun28.RealRatio
open Set Filter
open scoped Topology
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- Let the cyclic orbit be dense in G. If x is L-divisible in G, the
nonnegative multiples of Lg approach x at arbitrarily late indices. -/
theorem divisible_recurrence (g : G) (dense : DenseRange (fun j : ℤ => j • g))
    (L : ℕ) {x : G} (root : ∃ y : G, L • y=x) :
    MapClusterPt x atTop (fun k : ℕ => k • (L • g)) := by
  obtain ⟨y,rfl⟩:=root
  apply mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr
  change L • y∈closure ((AddSubgroup.zmultiples (L • g) : Set G))
  rw [AddSubgroup.coe_zmultiples]
  have incl : (fun v : G => L • v) '' range (fun j : ℤ => j • g) ⊆ range (fun j : ℤ => j • (L • g)) := by
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,smul_comm ..⟩
  exact closure_mono incl (image_closure_subset_closure_image (continuous_nsmul L) ⟨y,dense y,rfl⟩)

/-- Every tail visits every open neighborhood of this entire coset.
The subgroup can be a proper subtorus of the product of the two real curves. -/
theorem progression_visit (g : G) (dense : DenseRange (fun j : ℤ => j • g))
    (H : AddSubgroup G) (divide : ∀ (L : ℕ), 0<L → ∀ x∈H, ∃ y : G,L • y=x)
    (h₀ : ℤ) (L : ℕ) (positive : 0<L) {x : G} (component : x-h₀ • g∈H)
    {U : Set G} (opened : IsOpen U) (atx : x∈U) (lower : ℕ) :
    ∃ k : ℕ, lower≤k ∧ (h₀+(L:ℤ)*k) • g∈U := by
  have cp:=divisible_recurrence g dense L (divide L positive _ component)
  have op : IsOpen ((fun z : G => h₀ • g+z) ⁻¹' U) := opened.preimage (continuous_const.add continuous_id)
  have atz : x-h₀ • g ∈ ((fun z : G => h₀ • g+z) ⁻¹' U) := by simpa using atx
  obtain ⟨k,b,h⟩:=frequently_atTop.mp (cp.frequently (op.mem_nhds atz)) lower
  refine ⟨k,b,?_⟩
  change h₀ • g+k • L • g∈U at h
  convert h using 1
  rw [add_zsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℤ L g,← Nat.cast_smul_eq_nsmul ℤ k _,←mul_smul,mul_comm]

/-- Excluding a finite set of earlier indices is harmless, even for signed h₀. -/
theorem progression_avoid (g : G) (dense : DenseRange (fun j : ℤ => j • g))
    (H : AddSubgroup G) (divide : ∀ (L : ℕ), 0<L → ∀ x∈H, ∃ y : G,L • y=x)
    (h₀ : ℤ) (L : ℕ) (positive : 0<L) {x : G} (component : x-h₀ • g∈H)
    {U : Set G} (opened : IsOpen U) (atx : x∈U) {E : Set ℤ} (finite : E.Finite) (bound : ℤ) :
    ∃ (h : ℤ) (k : ℕ), h=h₀+(L:ℤ)*k ∧ bound<h ∧ h∉E ∧ h • g∈U := by
  obtain ⟨e,upper⟩:=finite.bddAbove
  let lower := (max e bound+1-h₀).toNat
  obtain ⟨k,hk,hs⟩:=progression_visit g dense H divide h₀ L positive component opened atx lower
  have grow : (k:ℤ)≤(L:ℤ)*k := by
    have pos : (1:ℤ)≤L := by exact_mod_cast positive
    simpa using mul_le_mul_of_nonneg_right pos (Int.natCast_nonneg k)
  have floor : max e bound+1-h₀ ≤ (lower:ℤ) := Int.self_le_toNat _
  have step : (lower:ℤ)≤k := by exact_mod_cast hk
  have hb : bound<h₀+(L:ℤ)*k := by omega
  have he : e<h₀+(L:ℤ)*k := by omega
  exact ⟨_,k,rfl,hb,fun mem => (not_le_of_gt he) (upper mem),hs⟩

/-- A finite list of arbitrary finite targets, including translates of both
embedded coordinates, discards finitely many integer indices under injective maps. -/
theorem finite_bad_indices {I Z : Type*} [Finite I] (f : I→ℤ→Z)
    (injective : ∀ i,Function.Injective (f i)) (bad : I→Set Z) (finite : ∀ i,(bad i).Finite) :
    (⋃ i, (f i) ⁻¹' bad i).Finite :=
  Set.finite_iUnion fun i => (finite i).preimage (injective i).injOn

end Sun28.RealRatio
#print axioms Sun28.RealRatio.divisible_recurrence
#print axioms Sun28.RealRatio.progression_visit
#print axioms Sun28.RealRatio.progression_avoid
#print axioms Sun28.RealRatio.finite_bad_indices
