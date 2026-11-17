import PrimitiveCells
namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

def dyadic := coordinates 2 16 (by decide)
def triadic := coordinates 3 9 (by decide)

def both (j:Fin 4) (t:(ZMod 16×ZMod 16)×(ZMod 9×ZMod 9)):Finset ℤ :=
  admissible j t.1.1 t.1.2 ∩ admissible j t.2.1 t.2.2

def joint (i:Fin 4) := (dyadic ×ˢ triadic).biUnion fun t=>
  both (rowsAt i 0) t ×ˢ (both (rowsAt i 1) t ×ˢ both (rowsAt i 2) t)

theorem joint_contains {x:ℚ} {i:Fin 4} (h:concentrated x i) : triples i x∈joint i := by
  obtain ⟨s,hs,sv⟩:=homogeneous_projective (x:=x) 2 16 (by decide) ⟨4,by decide⟩ (by decide)
  obtain ⟨t,ht,tv⟩:=homogeneous_projective (x:=x) 3 9 (by decide) ⟨2,by decide⟩ (by decide)
  have ok (j:Fin 3):coeff (rowsAt i j) x∈both (rowsAt i j) (s,t):=by
    obtain ⟨a,ha,ax⟩:=sv (rowsAt i j)
    obtain ⟨b,hb,bx⟩:=tv (rowsAt i j)
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨permitted h _,Finset.mem_image.mpr ⟨_,ha,ax⟩⟩,
      Finset.mem_filter.mpr ⟨permitted h _,Finset.mem_image.mpr ⟨_,hb,bx⟩⟩⟩
  exact Finset.mem_biUnion.mpr ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,Finset.mem_product.mpr
    ⟨ok 0,Finset.mem_product.mpr ⟨ok 1,ok 2⟩⟩⟩
end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.joint_contains
