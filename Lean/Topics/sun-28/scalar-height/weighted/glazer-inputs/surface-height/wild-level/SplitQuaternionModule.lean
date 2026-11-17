import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Morita equivalence for the two matrix units used in the non-CM descent. -/
namespace ZInQBlueprint.WildLevel
open Matrix
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def block (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (i j : Fin 2) :
    Module.End K V := β (Matrix.single i j 1)

private theorem blocks (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (i j k : Fin 2) (v:V) :
    block β i j (block β j k v) = block β i k v := by
  change (β _ * β _) v = β _ v
  rw [←map_mul]
  simp [Matrix.single_mul_single_same]

private theorem diagonal (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (v:V) :
    block β 0 0 v+block β 1 1 v=v := by
  have d : Matrix.single (0:Fin 2) (0:Fin 2) (1:K)+Matrix.single 1 1 1=1 := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  change ((β _)+(β _)) v=v
  rw [←map_add,d,map_one];rfl

private theorem different_blocks (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V)
    (i j k l : Fin 2) (h : j≠k) (v:V) : block β i j (block β k l v)=0 := by
  change (β _ * β _) v=0
  rw [←map_mul]
  simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

/-- The multiplicity space is the range of the first diagonal matrix unit. -/
abbrev firstBlock (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) := LinearMap.range (block β 0 0)

private def intoBlock (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (i : Fin 2) :
    V →ₗ[K] firstBlock β :=
  (block β 0 i).codRestrict _ fun v => ⟨block β 0 i v,blocks β 0 0 i v⟩

private theorem first_fixed (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (x : firstBlock β) :
    block β 0 0 (x:V)=x := by obtain ⟨v,h⟩:=x.property;rw [←h,blocks]

/-- Decomposition into two isomorphic summands with specified inverse
(x,y) ↦ x+E₁₀y. This works over any field. -/
def two_blocks (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) :
    V ≃ₗ[K] firstBlock β × firstBlock β where
  toFun v := (intoBlock β 0 v,intoBlock β 1 v)
  map_add' := by intros;ext <;> simp
  map_smul' := by intros;ext <;> simp
  invFun z := z.1.val + block β 1 0 z.2.val
  left_inv v := by change block β 0 0 v + block β 1 0 (block β 0 1 v)=v; rw [blocks,diagonal]
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext
    · change block β 0 0 _=_
      rw [map_add,first_fixed,different_blocks β 0 0 1 0 (by decide),add_zero]
    · change block β 0 1 _=_
      rw [map_add,blocks,first_fixed]
      obtain ⟨v,h⟩:=z.1.property
      rw [←h,different_blocks β 0 1 0 0 (by decide),zero_add]

theorem block_dimension [FiniteDimensional K V]
    (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (dim : Module.finrank K V=4) :
    Module.finrank K (firstBlock β)=2 := by
  have d := (two_blocks β).finrank_eq
  rw [Module.finrank_prod,dim] at d
  omega

/-- Every operator commuting with the split quaternion action acts by the
same restriction on the two copies. -/
theorem repeated_action (β : Matrix (Fin 2) (Fin 2) K →ₐ[K] Module.End K V) (T:V →ₗ[K] V)
    (compatible : ∀ (M:Matrix (Fin 2) (Fin 2) K) v,T (β M v)=β M (T v)) :
    ∃ S : firstBlock β →ₗ[K] firstBlock β,∀ v,
       two_blocks β (T v)=(S (two_blocks β v).1,S (two_blocks β v).2) := by
  let S := T.restrict (q:=firstBlock β) (p:=firstBlock β) (fun _ h=>by
    obtain ⟨v,rfl⟩:=h
    exact ⟨T v,(compatible _ v).symm⟩)
  refine ⟨S,fun v=>Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · exact (compatible _ v).symm
  · exact (compatible _ v).symm

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.two_blocks
#print axioms ZInQBlueprint.WildLevel.block_dimension
#print axioms ZInQBlueprint.WildLevel.repeated_action
