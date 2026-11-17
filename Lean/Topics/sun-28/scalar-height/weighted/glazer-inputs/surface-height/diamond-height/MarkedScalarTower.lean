import ScalarField
import Mathlib.FieldTheory.Galois.Basic

namespace ZInQBlueprint.DiamondHeight
noncomputable section

abbrev GQ := Field.absoluteGaloisGroup ℚ
abbrev Qbar := AlgebraicClosure ℚ

/-- The marking subgroup for an actual normal number field in the algebraic closure. -/
def markingGroup (L : IntermediateField ℚ Qbar) [IsGalois ℚ L] : Subgroup GQ :=
  (AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)).ker

theorem marking_index (L : IntermediateField ℚ Qbar) [IsGalois ℚ L] [FiniteDimensional ℚ L] :
    (markingGroup L).index=Module.finrank ℚ L := by
  change (AlgEquiv.restrictNormalHom L : (Qbar ≃ₐ[ℚ] Qbar) →* (L ≃ₐ[ℚ] L)).ker.index=_
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr
    (AlgEquiv.restrictNormalHom_surjective Qbar (K₁:=L) (F:=ℚ)),
    Nat.card_congr (Subgroup.topEquiv).toEquiv,IsGalois.card_aut_eq_finrank]

/-- On the marking subgroup, the scalar cochain is a character; conjugation
invariance makes its kernel normal in the full Galois group. -/
theorem normal_scalar_kernel {G K:Type*} [Group G] [Group K] (H:Subgroup G) [H.Normal]
    (b : H →* K) (inv : ∀ (g:G) (x:H),
      b ⟨g*(x:G)*g⁻¹,Subgroup.Normal.conj_mem (inferInstance : H.Normal) x x.2 g⟩=b x) : (b.ker.map H.subtype).Normal := by
  constructor
  intro a ha g
  obtain ⟨x,hx,rfl⟩:=ha
  exact ⟨⟨g*(x:G)*g⁻¹,Subgroup.Normal.conj_mem (inferInstance : H.Normal) x x.2 g⟩,
    (inv g x).trans hx,rfl⟩

/-- The order bound, degree bound, and normality fields of ScalarTower are
constructed from the signed local characters of (LR2) over the given field L. -/
def scalarTower_of_local_characters {R : ℕ} (L : IntermediateField ℚ Qbar)
    [IsGalois ℚ L] [FiniteDimensional ℚ L] (degree : Module.finrank ℚ L≤576)
    (dy : GQ →* ℂˣ) (dy2 : ∀ g, (dy g)^2=1)
    (ι : ∀ p:ℕ, GQ →* (ZMod p)ˣ) (χ : ∀ p:ℕ, (ZMod p)ˣ →* ℂˣ)
    (b : markingGroup L →* ℂˣ)
    (b2 : ∀ x, (b x)^2 = dy (x:GQ) * ∏ p ∈ R.primeFactors, χ p (ι p (x:GQ)))
    (inv : ∀ g x y, (y:markingGroup L).val = g*(x:markingGroup L).val*g⁻¹ → b y=b x)
    (det : GQ →* ℂˣ) (det2 : ∀ g ∈ b.ker.map (markingGroup L).subtype, (det g)^2=1) :
    ScalarTower R where
  marking := markingGroup L
  marking_pos := (marking_index L) ▸ Module.finrank_pos
  marking_degree := (marking_index L).trans_le degree
  m := 2*unitOrders R
  m_pos := by
    have pos : 0<unitOrders R := Finset.prod_pos fun p hp => by
      have q := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    omega
  order_bound := le_rfl
  scalar := b
  exponent_bound := fun x => by rw [pow_mul,b2];exact local_character_product R dy dy2 ι χ x.val
  normal := by
    let : (markingGroup L).Normal:=(AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)).normal_ker
    exact normal_scalar_kernel _ b (fun g x => inv g x _ rfl)
  determinant := det
  square := det2

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.marking_index
#print axioms ZInQBlueprint.DiamondHeight.normal_scalar_kernel
#print axioms ZInQBlueprint.DiamondHeight.scalarTower_of_local_characters
