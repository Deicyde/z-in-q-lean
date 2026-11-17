import ClusterPicture
/-! Geometric clusters, their children and the valuation sum for two triples. -/
namespace ZInQBlueprint.PrincipalClusters
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
noncomputable section
open ZInQBlueprint.ClusterPicture
abbrev Cluster := Finset Index
def row (i : Fin 2) : Cluster := Finset.univ.filter fun x => x.1=i
def tree : Finset Cluster := {Finset.univ,row 0,row 1} ∪ Finset.univ.image (fun r : Index => {r})
def children (s : Cluster) : Finset Cluster :=
  tree.filter fun t => t ⊂ s ∧ ∀ u ∈ tree, ¬(t ⊂ u ∧ u ⊂ s)

/-- The DDMM principal-cluster definition in genus two. -/
def principal (s : Cluster) : Prop :=
  s ∈ tree ∧ 3 ≤ s.card ∧ ¬(s=Finset.univ ∧ Even s.card ∧ (children s).card=2) ∧
    ∀ t ∈ children s, t.card ≠ 4

theorem row_children : ∀ i : Fin 2, children (row i) =
    (row i).image (fun r => ({r}:Cluster)) := by decide
theorem top_children : children Finset.univ = {row 0,row 1} := by decide

theorem principal_iff (s : Cluster) : principal s ↔ ∃ i, s=row i := by
  have h : ∀ t ∈ tree, (t.card ≥ 3 ∧ ¬(t=Finset.univ ∧ Even t.card ∧ (children t).card=2) ∧
    ∀ v ∈ children t, v.card ≠ 4) ↔ ∃ i, t=row i := by decide
  constructor
  · rintro ⟨hs,H⟩; exact (h s hs).mp H
  · rintro ⟨i,rfl⟩
    have hs : ∀ j, row j ∈ tree := by decide
    exact ⟨hs i,(h _ (hs i)).mpr ⟨i,rfl⟩⟩

theorem odd_subcluster : ∀ s ∈ tree, s ≠ Finset.univ → Odd s.card := by decide

/-- Smallest cluster containing the given cluster and the root. -/
def joinRoot (s : Cluster) (r : Index) : Cluster :=
  (tree.filter fun t => s ⊆ t ∧ r ∈ t).inf id

theorem join_row : ∀ (i : Fin 2) (r : Index),
    joinRoot (row i) r = if r.1=i then row i else Finset.univ := by decide
/-- Minimum pairwise valuation in a cluster, counting diagonal pairs at infinity. -/
def depth (dist : Index → Index → ℕ∞) (s : Cluster) : ℕ∞ :=
  (s ×ˢ s).inf fun ij => dist ij.1 ij.2

def table (m : ℕ) (i j : Index) : ℕ∞ :=
  if i=j then ⊤ else if i.1=j.1 then m else 0

theorem row_depth (m : ℕ) (i : Fin 2) : depth (table m) (row i)=m := by
  apply le_antisymm
  · have hh := Finset.inf_le (f:=fun xy : Index × Index => table m xy.1 xy.2)
        (show ((i,0),(i,1)) ∈ row i ×ˢ row i by simp [row])
    simpa [depth,table] using hh
  · apply Finset.le_inf
    intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hx
    simp [row] at hx hy
    by_cases he : x.1=x.2 <;> simp [table,hx,hy,he]

theorem top_depth (m : ℕ) : depth (table m) Finset.univ=0 := by
  apply le_antisymm _ (bot_le)
  have hh := Finset.inf_le (f:=fun xy : Index × Index => table m xy.1 xy.2)
    (show (((0,0):Index),((1,0):Index)) ∈ (Finset.univ:Cluster) ×ˢ Finset.univ by simp)
  simpa [depth,table] using hh

/-- DDMM's valuation sum on a principal cluster. Its joins have finite integral depth. -/
def nu (lead : ℤ) (dist : Index → Index → ℕ∞) (s : Cluster) (_hs : principal s) : ℤ :=
  lead + ∑ r : Index, (((depth dist (joinRoot s r)).toNat : ℕ):ℤ)

theorem principal_nu (lead : ℤ) (m : ℕ) {s : Cluster} (hs : principal s) :
    nu lead (table m) s hs=lead+3*m := by
  obtain ⟨i,rfl⟩ := (principal_iff _).mp hs
  rw [nu,← tripleNu_eq lead m i,tripleNu]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [join_row]; split_ifs <;> simp [row_depth,top_depth]

theorem mem_tree : ∀ s : Cluster, s∈tree ↔
    s=Finset.univ ∨ (∃ i, s=row i) ∨ ∃ r : Index, s={r} := by decide

theorem coe_row (i : Fin 2) : (row i : Set Index)={r | r.1=i} := by
  ext r
  simp [row]
section Geometry
open ZInQBlueprint.ClusterRoots
variable {R K Γ : Type*} [CommRing R] [IsLocalRing R] [CommRing K]
  [LinearOrderedAddCommMonoidWithTop Γ] {f : Polynomial R} {c : R}

def geometric (T : SexticFibre f c) (ι : R →+* K) (v : AddValuation K Γ) (s : Cluster) : Prop :=
  s.Nonempty ∧ ∃ z t, t<⊤ ∧ (s:Set Index)=disc T ι v z t

/-- Intersections with all geometric discs give exactly the nine members of the finite tree. -/
theorem geometric_iff (T : SexticFibre f c) (ι : R →+* K) (v : AddValuation K Γ)
    (hu : ∀ u : Rˣ, v (ι (u:R))=0) (hc : 0<v (ι c)) (hmore : ∃ t, v (ι c)<t ∧ t<⊤)
    (s : Cluster) : geometric T ι v s ↔ s∈tree := by
  obtain ⟨t₁,h₁,h₂⟩ := hmore
  have hit (b : Index) (t : Γ) : b ∈ disc T ι v (ι (point T b)) t := by
    change t ≤ v (_-_); simp
  rw [mem_tree]
  constructor
  · rintro ⟨⟨b,hb⟩,z,t,_,hs⟩
    have hd : b ∈ disc T ι v z t := by rw [← hs]; exact hb
    rw [classify T ι v hu hc z t hd] at hs
    split_ifs at hs with h h
    · exact Or.inl (Finset.coe_injective (hs.trans Finset.coe_univ.symm))
    · exact Or.inr (Or.inl ⟨b.1,Finset.coe_injective (hs.trans (coe_row _).symm)⟩)
    · exact Or.inr (Or.inr ⟨b,Finset.coe_injective (by simpa only [Finset.coe_singleton] using hs)⟩)
  · rintro (rfl | ⟨i,rfl⟩ | ⟨b,rfl⟩)
    · refine ⟨Finset.univ_nonempty,ι (point T (0,0)),0,lt_trans hc (lt_trans h₁ h₂),?_⟩
      rw [classify T ι v hu hc _ _ (hit (0,0) 0)]; simp
    · refine ⟨⟨(i,0),by simp [row]⟩,ι (point T (i,0)),v (ι c),lt_trans h₁ h₂,?_⟩
      rw [classify T ι v hu hc _ _ (hit (i,0) _)]
      simp [hc.not_ge,coe_row]
    · refine ⟨Finset.singleton_nonempty b,ι (point T b),t₁,h₂,?_⟩
      rw [classify T ι v hu hc _ _ (hit b t₁)]
      simp [(lt_trans hc h₁).not_ge,h₁.not_ge]
end Geometry

section
open IsDiscreteValuationRing ZInQBlueprint.ClusterRoots
variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {f : Polynomial S} {π : S}

theorem fibre_nu (hπ : Irreducible π) (m : ℕ) (T : SexticFibre f (π^m)) (lead : ℤ)
    {s : Cluster} (hs : principal s) :
    nu lead (fun i j => addVal S (point T i-point T j)) s hs=lead+3*m := by
  have h : (fun i j => addVal S (point T i-point T j))=table m :=
    funext fun i => funext fun j => dvr_distances hπ m T i j
  rw [h,principal_nu]
end

end
end ZInQBlueprint.PrincipalClusters
#print axioms ZInQBlueprint.PrincipalClusters.row_children
#print axioms ZInQBlueprint.PrincipalClusters.top_children
#print axioms ZInQBlueprint.PrincipalClusters.principal_iff
#print axioms ZInQBlueprint.PrincipalClusters.odd_subcluster
#print axioms ZInQBlueprint.PrincipalClusters.join_row
#print axioms ZInQBlueprint.PrincipalClusters.row_depth
#print axioms ZInQBlueprint.PrincipalClusters.top_depth
#print axioms ZInQBlueprint.PrincipalClusters.principal_nu
#print axioms ZInQBlueprint.PrincipalClusters.mem_tree
#print axioms ZInQBlueprint.PrincipalClusters.coe_row
#print axioms ZInQBlueprint.PrincipalClusters.geometric_iff
#print axioms ZInQBlueprint.PrincipalClusters.fibre_nu
