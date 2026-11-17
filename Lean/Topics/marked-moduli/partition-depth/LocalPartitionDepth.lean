import PartitionOrders
import RationalReduction

/-! Branch valuations on the charts of the twisted rational sextic. -/
namespace ZInQBlueprint.BranchDepth
open ClusterPicture ClusterRoots ResidueExtension RationalReduction
open Polynomial IsDiscreteValuationRing PrimitiveParameters IntegralSextic DirectCharts

noncomputable section
private def side (e : Fin 6 ≃ Index) (j : Fin 6) : Bool := decide ((e j).1 = 0)

private theorem side_card (e : Fin 6 ≃ Index) :
    (Finset.univ.filter (fun j => side e j = true)).card = 3 := by
  calc
    _ = (Finset.univ.filter (fun j : Index => j.1 = 0)).card :=
      Finset.card_bijective e e.bijective (fun i => by simp [side])
    _ = 3 := by decide

private theorem edge_side (a b : Fin 2) :
    (decide (a = 0) = decide (b = 0)) ↔ a=b := by decide +revert

/-- Every labeling of a two-triple Hensel fibre gives exactly the same multiset of orders. -/
theorem fibre_orders {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {f : S[X]} {π : S} (hπ : Irreducible π) (m : ℕ) (T : SexticFibre f (π^m))
    (e : Fin 6 ≃ Index) :
    ∃ k : Fin 10, ∀ i, addVal S (weight (fun j => point T (e j)) i) =
      if i = k then ((12*m : ℕ) : ℕ∞) else ((4*m : ℕ) : ℕ∞) := by
  obtain ⟨k,hk⟩ := orders (addVal S) (fun j => point T (e j)) (m : ℕ∞)
    (side e) (side_card e) (by
      intro i j hn
      rw [dvr_distances hπ m T]
      simp only [e.injective.ne hn,↓reduceIte]
      simp only [sameEdge,side,edge_side]
      split <;> simp)
  exact ⟨k,fun i => by simpa only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] using hk i⟩

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

/-- The chart coordinates and all ten orders at every positive even contact of the rational input. -/
theorem even_contact_orders (u : ℚ) (hp : 17 ≤ p) (m : ℕ) (hm : 0 < m)
    (hF : addVal Zp (RationalClusters.F p u) = ((2*m : ℕ) : ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^m),
        ∀ e : Fin 6 ≃ Index, ∃ k : Fin 10, ∀ i, addVal W (weight (fun j => point T (e j)) i) =
          if i=k then ((12*m : ℕ) : ℕ∞) else ((4*m : ℕ) : ℕ∞) := by
  obtain ⟨t,v,a,hc,T,_⟩ := even_contact_chart p u hp m hm hF
  exact ⟨t,v,a,hc,T,fibre_orders (uniformizer p) m T⟩

/-- At a pole the same integral chart has depths given by the valuation of G. -/
theorem pole_orders (u : ℚ) (hp : 17 ≤ p) (m : ℕ) (hm : 0 < m)
    (hG : addVal Zp (RationalClusters.G p u) = (m : ℕ∞)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p (t:Zp))) ((p:W)^m),
        ∀ e : Fin 6 ≃ Index, ∃ k : Fin 10, ∀ i, addVal W (weight (fun j => point T (e j)) i) =
          if i=k then ((12*m : ℕ) : ℕ∞) else ((4*m : ℕ) : ℕ∞) := by
  obtain ⟨t,a,hc,T,_,_⟩ := pole_chart p u hp m hm hG
  exact ⟨t,a,hc,T,fibre_orders (uniformizer p) m T⟩

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.fibre_orders
#print axioms ZInQBlueprint.BranchDepth.even_contact_orders
#print axioms ZInQBlueprint.BranchDepth.pole_orders
