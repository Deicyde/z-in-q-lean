import EtaleEvaluation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.FieldTheory.Galois.Basic

namespace ZInQBlueprint.LevelExtension
open NumberField IntermediateField Function
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {S : Type*} [CommRing S] [Algebra (away K) S]
variable {Γ : Type*} [Group Γ]

omit [NumberField L] in
/-- One geometric point of a constant deck torsor generates the field of the whole
fibre. The deck transformations are endomorphisms of the very same coordinate algebra. -/
theorem one_point_generates (lab : Γ ≃ (S →ₐ[away K] L)) (T : Γ → S →ₐ[away K] S)
    (deck : ∀ a b,lab (a*b)=(lab b).comp (T a)) (gen : Generates (Set.univ : Set (S →ₐ[away K] L)))
    (h : Γ) : Generates ({lab h} : Set (S →ₐ[away K] L)) := by
  apply top_unique
  rw [←(gen : adjoin K _ = ⊤),adjoin_le_iff]
  rintro _ ⟨f,_,a,rfl⟩
  obtain ⟨i,rfl⟩:=lab.surjective f
  have pt : lab i = (lab h).comp (T (i*h⁻¹)) := by simpa only [inv_mul_cancel_right] using deck (i*h⁻¹) h
  exact subset_adjoin _ _ ⟨lab h,Set.mem_singleton _,T (i*h⁻¹) a, by rw [pt];rfl⟩

private def post (σ : L ≃ₐ[K] L) (f : S →ₐ[away K] L) : S →ₐ[away K] L :=
  ({σ.toRingHom with commutes' := fun r=>σ.commutes (r:K)} : L →ₐ[away K] L).comp f

/-- The Galois degree over the coarse field divides the order of the relative deck
group, with the Galois action induced by field automorphisms on point coordinates. -/
theorem degree_dvd_deck [IsGalois K L] [Fintype Γ] (lab : Γ ≃ (S →ₐ[away K] L))
    (T : Γ → S →ₐ[away K] S) (deck : ∀ a b,lab (a*b)=(lab b).comp (T a))
    (gen : Generates (Set.univ : Set (S →ₐ[away K] L))) : Module.finrank K L ∣ Fintype.card Γ := by
  let v (σ : L ≃ₐ[K] L) := lab.symm (post σ (lab 1))
  have post_lab (σ : L ≃ₐ[K] L) (i : Γ) : post σ (lab i)=lab (i*v σ) := by
    rw [deck i (v σ),show lab (v σ)=post σ (lab 1) from lab.apply_symm_apply _]
    have e : lab i=(lab 1).comp (T i) := by simpa only [mul_one] using deck i 1
    rw [e]
    rfl
  let embed : (L ≃ₐ[K] L) →* Γ := {
    toFun := fun σ => (v σ)⁻¹
    map_one' := by
      have r : post (1 : L ≃ₐ[K] L) (lab 1) = lab 1 := by ext; rfl
      simp [v,r]
    map_mul' := by
      intro σ τ
      change (lab.symm (post σ (post τ (lab 1))))⁻¹=(v σ)⁻¹*(v τ)⁻¹
      rw [← show lab (v τ)=post τ (lab 1) from lab.apply_symm_apply _,post_lab,lab.symm_apply_apply,mul_inv_rev] }
  have injective : Injective embed := by
    intro σ τ eqv
    have vv : v σ=v τ := inv_injective (show (v σ)⁻¹=(v τ)⁻¹ from eqv)
    have all (f : S →ₐ[away K] L) (a : S) : σ (f a)=τ (f a) := by
      obtain ⟨i,rfl⟩:=lab.surjective f
      exact congrArg (fun f : S →ₐ[away K] L => f a) ((post_lab σ i).trans ((vv ▸ post_lab τ i).symm))
    ext z
    have ht : z∈adjoin K {x:L | ∃ f∈(Set.univ:Set (S →ₐ[away K] L)),∃a:S,f a=x} := by rw [gen];trivial
    induction ht using adjoin_induction with
    | mem x hx => obtain ⟨f,_,a,rfl⟩:=hx; exact all f a
    | algebraMap a => rw [σ.commutes,τ.commutes]
    | add x y _ _ hx hy => rw [map_add,map_add,hx,hy]
    | inv x _ hx => rw [map_inv₀,map_inv₀,hx]
    | mul x y _ _ hx hy => rw [map_mul,map_mul,hx,hy]
  rw [←IsGalois.card_aut_eq_finrank K L,←Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective embed injective

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.one_point_generates
#print axioms ZInQBlueprint.LevelExtension.degree_dvd_deck
