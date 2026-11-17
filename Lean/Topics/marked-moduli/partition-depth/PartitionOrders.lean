import BranchRows
import ClusterPicture

/-! Valuations of the ten products of two squared Vandermonde determinants. -/
namespace ZInQBlueprint.BranchDepth
open BranchFormula
noncomputable section

def triangle {R : Type*} [CommRing R] (r : Fin 6 → R) (a b c : Fin 6) : R :=
  (r a-r b)*(r a-r c)*(r b-r c)

def weight {R : Type*} [CommRing R] (r : Fin 6 → R) (i : Fin 10) : R :=
  let t := row i
  (triangle r t.p.castSucc t.q.castSucc 5 *
    triangle r t.a.castSucc t.b.castSucc t.c.castSucc)^2

theorem complex_weight (r : Fin 6 → ℂ) (i : Fin 10) : weight r i = rowWeight r i := rfl

private theorem distinct_vertices (i : Fin 10) :
    (row i).p.castSucc ≠ (row i).q.castSucc ∧ (row i).p.castSucc ≠ (5 : Fin 6) ∧
    (row i).q.castSucc ≠ (5 : Fin 6) ∧ (row i).a.castSucc ≠ (row i).b.castSucc ∧
    (row i).a.castSucc ≠ (row i).c.castSucc ∧ (row i).b.castSucc ≠ (row i).c.castSucc := by
  decide +revert

def sameEdge (side : Fin 6 → Bool) (i j : Fin 6) : ℕ := if side i = side j then 1 else 0

def inside (side : Fin 6 → Bool) (a b c : Fin 6) : ℕ :=
  sameEdge side a b + sameEdge side a c + sameEdge side b c

def withinEdges (side : Fin 6 → Bool) (i : Fin 10) : ℕ :=
  let t := row i
  inside side t.p.castSucc t.q.castSucc 5 + inside side t.a.castSucc t.b.castSucc t.c.castSucc

theorem three_three_counts (side : Fin 6 → Bool)
    (hs : (Finset.univ.filter (fun j => side j = true)).card = 3) :
    ∃ k : Fin 10, ∀ i, withinEdges side i = if i = k then 6 else 2 := by
  decide +revert

private theorem triangle_order {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) (r : Fin 6 → R) (d : Γ) (s : Fin 6 → Bool)
    (h : ∀ i j, i ≠ j → v (r i-r j) = sameEdge s i j • d)
    {a b c : Fin 6} (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    v (triangle r a b c) = inside s a b c • d := by
  simp only [triangle,inside,v.map_mul,h a b hab,h a c hac,h b c hbc,add_nsmul]

theorem weight_order {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) (r : Fin 6 → R) (d : Γ) (s : Fin 6 → Bool)
    (h : ∀ i j, i ≠ j → v (r i-r j) = sameEdge s i j • d) (i : Fin 10) :
    v (weight r i) = (2*withinEdges s i) • d := by
  obtain ⟨hpq,hp,hq,hab,hac,hbc⟩ := distinct_vertices i
  simp only [weight,withinEdges,v.map_pow,v.map_mul,triangle_order v r d s h hpq hp hq,
    triangle_order v r d s h hab hac hbc,← add_nsmul,← mul_nsmul]
  rw [Nat.mul_comm]

/-- One partition has valuation 12d and the other nine have valuation 4d. -/
theorem orders {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) (r : Fin 6 → R) (d : Γ) (s : Fin 6 → Bool)
    (hs : (Finset.univ.filter (fun j => s j = true)).card = 3)
    (h : ∀ i j, i ≠ j → v (r i-r j) = sameEdge s i j • d) :
    ∃ k : Fin 10, ∀ i, v (weight r i) = if i = k then 12 • d else 4 • d := by
  obtain ⟨k,hk⟩ := three_three_counts s hs
  refine ⟨k,fun i => ?_⟩
  rw [weight_order v r d s h,hk]
  split <;> rfl

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.complex_weight
#print axioms ZInQBlueprint.BranchDepth.three_three_counts
#print axioms ZInQBlueprint.BranchDepth.weight_order
#print axioms ZInQBlueprint.BranchDepth.orders
