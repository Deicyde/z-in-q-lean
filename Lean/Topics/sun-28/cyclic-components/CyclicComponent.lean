import CompactMultiples

namespace Sun28.CyclicOrbit
open Set Filter
open scoped Topology
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- The group in which the recurrence argument is applied is the actual cyclic closure. -/
abbrev orbitClosure (g : G) : AddSubgroup G := (AddSubgroup.zmultiples g).topologicalClosure

def generator (g : G) : orbitClosure g :=
  ⟨g, (AddSubgroup.zmultiples g).le_topologicalClosure (AddSubgroup.mem_zmultiples g)⟩

/-- Density follows from the definition of the closure. -/
theorem dense_generator (g : G) : DenseRange (fun m : ℤ => m • generator g) := by
  apply Subtype.dense_iff.mpr
  have eq : Subtype.val '' Set.range (fun m : ℤ => m • generator g) = Set.range (fun m : ℤ => m • g) := by
    ext x
    constructor
    · rintro ⟨_,⟨m,rfl⟩,rfl⟩
      exact ⟨m,rfl⟩
    · rintro ⟨m,rfl⟩
      exact ⟨m • generator g,⟨m,rfl⟩,rfl⟩
  change (orbitClosure g : Set G) ⊆ closure ((Subtype.val : orbitClosure g → G) '' Set.range (fun m : ℤ => m • generator g))
  exact (congrArg closure eq).symm ▸ (show (orbitClosure g : Set G) ⊆ closure (Set.range (fun m : ℤ => m • g)) by
    rw [← AddSubgroup.coe_zmultiples]
    exact Set.Subset.rfl)

instance orbitCompact [CompactSpace G] (g : G) : CompactSpace (orbitClosure g) :=
  isCompact_iff_compactSpace.mp (AddSubgroup.isClosed_topologicalClosure _).isCompact

/-- A neighborhood of zero in a compact group contains arbitrarily large multiples. -/
theorem positive_return [CompactSpace G] (g : G) {U : Set G} (nbhd : U ∈ 𝓝 (0:G)) :
    ∃ q : ℕ, 0<q ∧ q • g∈U := by
  have cp : MapClusterPt (0:G) atTop (fun n : ℕ => n • g) :=
    mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr ((orbitClosure g).zero_mem)
  obtain ⟨q,pos,hq⟩ := frequently_atTop.mp (cp.frequently nbhd) 1
  exact ⟨q,pos,hq⟩

/-- Openness of the identity component suffices to construct all the orbit data.
No dimension, period, independent generators, or torus classification enters. -/
noncomputable def of_open_component [CompactSpace G] [T2Space G] (g : G)
    (op : IsOpen (connectedComponent (0 : orbitClosure g))) : RealRatio.Orbit (orbitClosure g) := by
  classical
  let G₀ := AddSubgroup.connectedComponentOfZero (orbitClosure g)
  have ret := positive_return (generator g) (op.mem_nhds mem_connectedComponent)
  exact { generator := generator g
          dense := dense_generator g
          H := G₀
          q := ret.choose
          positive := ret.choose_spec.1
          step := by
            change (ret.choose : ℤ) • generator g ∈ connectedComponent (0 : orbitClosure g)
            simpa only [Nat.cast_smul_eq_nsmul] using ret.choose_spec.2
          divide := fun L l x hx => component_root (generator g) (dense_generator g) l hx }

/-- Local connectedness of the cyclic closure suffices for the required orbit. -/
noncomputable def of_locally_connected [CompactSpace G] [T2Space G] (g : G)
    [LocallyConnectedSpace (orbitClosure g)] : RealRatio.Orbit (orbitClosure g) :=
  of_open_component g isOpen_connectedComponent

theorem generator_value [CompactSpace G] [T2Space G] (g : G)
    (op : IsOpen (connectedComponent (0 : orbitClosure g))) :
    ((of_open_component g op).generator : G) = g := rfl

end Sun28.CyclicOrbit

#print axioms Sun28.CyclicOrbit.dense_generator
#print axioms Sun28.CyclicOrbit.orbitCompact
#print axioms Sun28.CyclicOrbit.positive_return
#print axioms Sun28.CyclicOrbit.of_open_component
#print axioms Sun28.CyclicOrbit.of_locally_connected
#print axioms Sun28.CyclicOrbit.generator_value
