import CompactWindows
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Connected.LocallyConnected

namespace Sun28.CyclicOrbit
open Set
open scoped Topology
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G]

/-- The power image is closed by compactness. -/
theorem closed_multiples (L : ℕ) : IsClosed (Set.range (fun y : G => L • y)) :=
  (isCompact_range (continuous_nsmul L)).isClosed

/-- Each translate of the power image is closed. -/
theorem closed_coset (g : G) (L : ℕ) (a : ℤ) :
    IsClosed (Set.range (fun y : G => a • g + L • y)) :=
  (isCompact_range (continuous_const.add (continuous_nsmul L))).isClosed

/-- The L residue classes cover the whole group, by density of the integer orbit. -/
theorem residue_cover (g : G) (dense : DenseRange (fun m : ℤ => m • g))
    {L : ℕ} (pos : 0 < L) :
    ∀ x : G, ∃ a : Fin L, ∃ y : G, (a.val : ℤ) • g + L • y = x := by
  let F (a : Fin L) := Set.range (fun y : G => (a.val : ℤ) • g + L • y)
  have closed : IsClosed (⋃ a, F a) := isClosed_iUnion_of_finite (fun a => closed_coset g L a.val)
  have includes : Set.range (fun m : ℤ => m • g) ⊆ ⋃ a, F a := by
    rintro _ ⟨m,rfl⟩
    let r := m % (L:ℤ)
    have rp : 0≤r := Int.emod_nonneg _ (by exact_mod_cast pos.ne')
    have rl : r<(L:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast pos)
    let a : Fin L := ⟨r.toNat, by omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, (m/(L:ℤ)) • g, ?_⟩
    have eq : (a.val:ℤ)=m % (L:ℤ) := Int.toNat_of_nonneg rp
    change (a.val:ℤ) • g + L • ((m/(L:ℤ)) • g) = m • g
    rw [eq, ← Nat.cast_smul_eq_nsmul ℤ L, ←mul_smul, ←add_zsmul, Int.emod_add_mul_ediv]
  intro x
  exact Set.mem_iUnion.mp (closed.closure_subset_iff.mpr includes (dense x))

/-- In a compact Hausdorff monothetic group a positive multiple has open image. -/
theorem open_multiples (g : G) (dense : DenseRange (fun m : ℤ => m • g))
    {L : ℕ} (pos : 0<L) : IsOpen (Set.range (fun y : G => L • y)) := by
  classical
  let H := (nsmulAddMonoidHom (α := G) L).range
  have onto : Function.Surjective (fun a : Fin L => QuotientAddGroup.mk' H ((a.val:ℤ) • g)) := by
    intro v
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective H v
    obtain ⟨a,y,rfl⟩ := residue_cover g dense pos x
    refine ⟨a,?_⟩
    have zero : QuotientAddGroup.mk' H (L • y)=0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨y,rfl⟩
    rw [map_add,zero,add_zero]
  let : Finite (G ⧸ H) := Finite.of_surjective _ onto
  let : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact H.isOpen_of_isClosed_of_finiteIndex (closed_multiples L)

/-- The application only needs divisibility in the ambient group. Every point
of the identity component belongs to each positive power image. -/
theorem component_root (g : G) (dense : DenseRange (fun m : ℤ => m • g))
    {L : ℕ} (pos : 0<L) {x : G} (hx : x∈connectedComponent (0:G)) :
    ∃ y : G, L • y = x := by
  have clopen : IsClopen (Set.range (fun y : G => L • y)) := ⟨closed_multiples L,open_multiples g dense pos⟩
  exact clopen.connectedComponent_subset (show (0:G) ∈ Set.range (fun y : G => L • y) from
    ⟨0,nsmul_zero L⟩) hx

end Sun28.CyclicOrbit

#print axioms Sun28.CyclicOrbit.closed_multiples
#print axioms Sun28.CyclicOrbit.closed_coset
#print axioms Sun28.CyclicOrbit.residue_cover
#print axioms Sun28.CyclicOrbit.open_multiples
#print axioms Sun28.CyclicOrbit.component_root
