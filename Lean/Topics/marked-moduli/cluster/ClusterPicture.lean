import ClusterRoots
import Mathlib.RingTheory.DiscreteValuationRing.Basic
/-! Closed discs of the six roots and the principal-cluster valuation. -/
namespace ZInQBlueprint.ClusterPicture
open Polynomial IsLocalRing ZInQBlueprint.ClusterRoots
noncomputable section
abbrev Index := Fin 2 × Fin 3
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] {f : R[X]} {c : R}
def point (T : SexticFibre f c) (i : Index) : R := T.centres i.1+c*T.triples.y i.1 i.2
variable {K Γ : Type*} [CommRing K] [LinearOrderedAddCommMonoidWithTop Γ]
omit [IsDomain R] in
theorem distances (T : SexticFibre f c) (ι : R →+* K) (v : AddValuation K Γ)
    (hunit : ∀ u : Rˣ, v (ι (u:R))=0) (i j : Index) :
    v (ι (point T i)-ι (point T j)) =
      if i=j then ⊤ else if i.1=j.1 then v (ι c) else 0 := by
  classical
  rcases i with ⟨i,s⟩
  rcases j with ⟨k,l⟩
  by_cases h : i=k
  · subst k
    by_cases h' : s=l
    · subst l; simp
    · obtain ⟨u,hu⟩ := T.triples.within i s l h'
      rw [← map_sub,show point T (i,s)-point T (i,l)=c*(u:R) from hu,map_mul,v.map_mul,hunit]
      simp [h']
  · obtain ⟨u,hu⟩ := T.triples.across i k h s l
    rw [← map_sub,show point T (i,s)-point T (k,l)=(u:R) from hu.symm,hunit]
    simp [h]

theorem recenter (v : AddValuation K Γ) (x b z : K) (t : Γ) (hb : t ≤ v (b-z)) :
    t ≤ v (x-z) ↔ t ≤ v (x-b) := by
  constructor
  · intro hx
    have hb' : t ≤ v (z-b) := by rwa [v.map_sub_swap]
    simpa only [sub_add_sub_cancel] using v.map_le_add hx hb'
  · intro hx
    simpa only [sub_add_sub_cancel] using v.map_le_add hx hb

def disc (T : SexticFibre f c) (ι : R →+* K) (v : AddValuation K Γ) (z : K) (t : Γ) :
    Set Index := {i | t ≤ v (ι (point T i)-z)}

omit [IsDomain R] in
/-- All nonempty intersections with geometric closed discs, including fractional depths. -/
theorem classify (T : SexticFibre f c) (ι : R →+* K) (v : AddValuation K Γ)
    (hunit : ∀ u : Rˣ, v (ι (u:R))=0) (hc : 0 < v (ι c)) (z : K) (t : Γ)
    {b : Index} (hb : b ∈ disc T ι v z t) :
    disc T ι v z t = if t ≤ 0 then Set.univ else
      if t ≤ v (ι c) then {i | i.1=b.1} else {b} := by
  classical
  ext i
  change (t ≤ v (ι (point T i)-z)) ↔ _
  rw [recenter v _ _ _ _ hb,distances T ι v hunit]
  by_cases hi : i=b
  · subst i; split_ifs <;> simp_all
  · by_cases hj : i.1=b.1 <;> split_ifs <;> simp_all
    all_goals order

section
variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
open IsDiscreteValuationRing
/-- Within one triple the normalized depth is the power of the uniformizer. -/
theorem dvr_distances {F : S[X]} {π : S} (hπ : Irreducible π) (m : ℕ)
    (T : SexticFibre F (π^m)) (i j : Index) :
    addVal S (point T i-point T j) =
      if i=j then ⊤ else if i.1=j.1 then (m:ℕ∞) else 0 := by
  simpa only [RingHom.id_apply,hπ.addVal_pow] using
    distances T (RingHom.id S) (addVal S) addVal_eq_zero_of_unit i j

end

/-- For a triple the joins with its three members have depth m; the three
other joins are the top cluster of depth zero. -/
def tripleNu (lead m : ℤ) (i : Fin 2) : ℤ :=
  lead+∑ x : Index, (if x.1=i then m else 0)

theorem tripleNu_eq (lead m : ℤ) (i : Fin 2) : tripleNu lead m i = lead+3*m := by
  fin_cases i <;> simp [tripleNu,Fintype.sum_prod_type,Fin.sum_univ_succ] <;> ring

theorem contact_parity (k : ℤ) (i : Fin 2) : Even (tripleNu (k%2) k i) := by
  rw [tripleNu_eq,Int.even_iff]
  omega

theorem pole_nu (g : ℤ) (i : Fin 2) : tripleNu (-3*g) g i = 0 := by
  rw [tripleNu_eq]; ring

end
end ZInQBlueprint.ClusterPicture
#print axioms ZInQBlueprint.ClusterPicture.distances
#print axioms ZInQBlueprint.ClusterPicture.recenter
#print axioms ZInQBlueprint.ClusterPicture.classify
#print axioms ZInQBlueprint.ClusterPicture.dvr_distances
#print axioms ZInQBlueprint.ClusterPicture.tripleNu_eq
#print axioms ZInQBlueprint.ClusterPicture.contact_parity
#print axioms ZInQBlueprint.ClusterPicture.pole_nu
