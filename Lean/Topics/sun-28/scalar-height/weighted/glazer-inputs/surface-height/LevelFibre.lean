import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-! The arithmetic Galois action on the full level-three fibre commutes with the deck group. -/
namespace ZInQBlueprint.FiveMetric
open Function
noncomputable section

/-- Evaluation at the identity identifies the centralizer of left translations
with right translations. An inverse accounts for the order of composition. -/
theorem torsor_image_dvd {G Γ : Type*} [Group G] [Group Γ] [Fintype Γ]
    (ρ:G →* Equiv.Perm Γ) (deck : ∀ g a b,ρ g (a*b)=a*ρ g b) :
    Nat.card (G ⧸ ρ.ker) ∣ Fintype.card Γ := by
  let f : ρ.range →* Γ := {
    toFun := fun u=>(u.val 1)⁻¹
    map_one' := by simp
    map_mul' := by
      rintro ⟨_,g,rfl⟩ ⟨_,h,rfl⟩
      change (ρ g (ρ h 1))⁻¹=(ρ g 1)⁻¹*(ρ h 1)⁻¹
      rw [←mul_one (ρ h 1),deck, mul_one, mul_inv_rev] }
  have faithful : Injective f := by
    rintro ⟨_,g,rfl⟩ ⟨_,h,rfl⟩ he
    change (ρ g 1)⁻¹=(ρ h 1)⁻¹ at he
    apply Subtype.ext
    ext a
    simpa only [mul_one] using (deck g a 1).trans ((congrArg (a*·) (inv_injective he)).trans (deck h a 1).symm)
  have groupCard:=Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  rw [groupCard,←Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective f faithful

/-- Specialization to the geometric fibre of size 36 times 16, with its actual splitting action. -/
theorem level_three_degree {G Γ : Type*} [Group G] [Group Γ] [Fintype Γ]
    (size : Fintype.card Γ=36*16) (ρ:G →* Equiv.Perm Γ)
    (deck : ∀ g a b,ρ g (a*b)=a*ρ g b) : Nat.card (G ⧸ ρ.ker) ∣ 576 := by
  simpa only [size] using torsor_image_dvd ρ deck

end
end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.torsor_image_dvd
#print axioms ZInQBlueprint.FiveMetric.level_three_degree
