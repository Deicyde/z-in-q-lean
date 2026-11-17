import ProjectiveRows

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def compatible (i:Fin 4) (p n:ℕ) [NeZero n] (pn:p∣n) (kl:ℤ×ℤ×ℤ):Prop :=
  ∃ t∈coordinates p n pn, possible n (rowsAt i 0) t.1 t.2 kl.1 ∧
    possible n (rowsAt i 1) t.1 t.2 kl.2.1 ∧ possible n (rowsAt i 2) t.1 t.2 kl.2.2

instance {n:ℕ} [NeZero n] {i:Fin 4} {a b:ZMod n} {k:ℤ}: Decidable (possible n i a b k) := by
  unfold possible;infer_instance
instance {i:Fin 4} {p n:ℕ} [NeZero n] {pn:p∣n} {k:ℤ×ℤ×ℤ}:Decidable (compatible i p n pn k) := by
  unfold compatible;infer_instance

theorem effective_filter (x:ℚ) (i:Fin 4) (p n:ℕ) [NeZero n] (pp:p.Prime)
    (power:∃e:ℕ,n=p^e) (pn:p∣n) : compatible i p n pn (triples i x) := by
  obtain ⟨t,mt,ev⟩:=homogeneous_projective (x:=x) p n pp power pn
  exact ⟨t,mt,ev _,ev _,ev _⟩

def okCell (i:Fin 4) (p n:ℕ) [NeZero n] (pn:p∣n) :=
  (coordinates p n pn).biUnion fun t=>admissible (rowsAt i 0) t.1 t.2 ×ˢ
    (admissible (rowsAt i 1) t.1 t.2 ×ˢ admissible (rowsAt i 2) t.1 t.2)

theorem cell_contains {i:Fin 4} {x:ℚ} (h:concentrated x i) (p n:ℕ) [NeZero n]
    (pp:p.Prime) (power:∃e:ℕ,n=p^e) (pn:p∣n): triples i x∈okCell i p n pn := by
  obtain ⟨t,ht,ev⟩:=homogeneous_projective (x:=x) p n pp power pn
  have ok (j:Fin 3):coeff (rowsAt i j) x∈admissible (rowsAt i j) t.1 t.2:=by
    obtain ⟨z,hz,eq⟩:=ev (rowsAt i j)
    exact Finset.mem_filter.mpr ⟨permitted h _,Finset.mem_image.mpr ⟨_,hz,eq⟩⟩
  exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_product.mpr ⟨ok 0,Finset.mem_product.mpr ⟨ok 1,ok 2⟩⟩⟩

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.effective_filter
#print axioms Sun28.FactorHeights.cell_contains
