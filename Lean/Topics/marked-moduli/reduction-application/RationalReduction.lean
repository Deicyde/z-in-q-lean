import PrimitiveParameters
import PrimitiveRoots
import PrimitivePoleFibre
/-! The arithmetic of the rational equation at the good-reduction primes. -/
namespace ZInQBlueprint.RationalReduction
open Polynomial IsDiscreteValuationRing
open ZInQBlueprint.ResidueExtension ZInQBlueprint.PrimitiveParameters ZInQBlueprint.LeadingOrders
open ZInQBlueprint.GlobalTwist ZInQBlueprint.DirectCharts ZInQBlueprint.PrincipalClusters
open ZInQBlueprint.ClusterPicture ZInQBlueprint.ClusterRoots ZInQBlueprint.RationalClusters
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

def equation (u : ℚ) (v a : Zpˣ) (t : Zp) : W[X] :=
  chart (delta u:W) (fromPadics p (G p u)) (fromPadics p (v:Zp)) (fromPadics p (a:Zp)) (fromPadics p t)

theorem roots {S K : Type*} [CommRing S] [IsDomain S] [IsLocalRing S] [CommRing K] [IsDomain K]
    {f : S[X]} {c l : S} (T : SexticFibre f c) (hl : l≠0) (ι : S →+* K)
    (hi : Function.Injective ι) (z : K) :
    ((C l*f).map ι).IsRoot z ↔ ∃ i : Index, z=ι (point T i) := by
  have h := (map_ne_zero_iff ι hi).mpr hl
  calc
    _ ↔ (f.map ι).IsRoot z := by simp [IsRoot,h]
    _ ↔ _ := by
      rw [root_iff T ι hi]
      exact ⟨fun ⟨i,j,hj⟩ => ⟨(i,j),hj⟩,fun ⟨⟨i,j⟩,hj⟩ => ⟨i,j,hj⟩⟩

def conditions {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {f : S[X]} {c : S}
    (scaled : S[X]) (T : SexticFibre f c) (l : ℕ) : Prop :=
  addVal S scaled.leadingCoeff=(l:ℕ∞) ∧
  (∀ s∈tree, s≠Finset.univ → Odd s.card) ∧ ∀ s (hs : principal s), Even (principalOrder scaled T s hs)

theorem even_contact_chart (u : ℚ) (hp : 17≤p) (k : ℕ) (hk : 0<k)
    (hf : addVal Zp (F p u)=((2*k:ℕ):ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^k), conditions (equation p u v a t) T (k%2) := by
  obtain ⟨t,v,a,hc,ht⟩ := even_parameter p u hp k hk hf
  obtain ⟨T⟩ := PrimitiveRoots.even_valuation p (by omega) t k hk ht
  exact ⟨t,v,a,hc,T,even_lead p u hp k hk hf (v.isUnit.map _) (a.isUnit.map _) _,odd_subcluster,
    fun s hs => even_principal p u hp k hk hf (v.isUnit.map _) (a.isUnit.map _) T s hs⟩
theorem pole_chart (u : ℚ) (hp : 17≤p) (g : ℕ) (hg : 0<g)
    (hG : addVal Zp (G p u)=(g:ℕ∞)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p (t:Zp))) ((p:W)^g),
        conditions (equation p u 1 a t) T g ∧
        ∀ s (hs : principal s), principalOrder (equation p u 1 a t) T s hs=4*g := by
  obtain ⟨t,a,hc,_⟩ := PrimitiveParameters.pole_parameter p u hp g hg hG
  have ht : (t:Zp)*left p u=right p u := by
    cases hc with
    | first _ ha h => rw [←ha,mul_comm]; exact h
    | second hv _ _ => norm_num at hv
  obtain ⟨T⟩ := PrimitivePoleFibre.pole_parameter p (by omega) _ _ (t:Zp)
    (PadicParameters.rational_primitive u) g hg hG ht
  have h1 := (1:Zpˣ).isUnit.map (fromPadics p)
  have hn (s) (hs : principal s) : principalOrder (equation p u 1 a t) T s hs=4*g :=
    pole_principal p u hp g hg hG h1 (a.isUnit.map _) T s hs
  exact ⟨t,a,hc,T,⟨pole_lead p u hp g hg hG h1 (a.isUnit.map _) _,odd_subcluster,
    fun s hs => by rw [hn s hs,Int.even_iff]; omega⟩,hn⟩

end
end ZInQBlueprint.RationalReduction
#print axioms ZInQBlueprint.RationalReduction.roots
#print axioms ZInQBlueprint.RationalReduction.even_contact_chart
#print axioms ZInQBlueprint.RationalReduction.pole_chart
