import GenusTwoHeight
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Finer descent to points on one fixed genus-two curve over a tagged
biquadratic field. Square classes are detected by the two Galois signs. -/
namespace Sun28.FiveDescent
open Sun28.Ordinary Sun28.FiveMarkUnits Height
noncomputable section

/-- The two-parameter twists become the single curve V²=cubic(Z²).
The marked rational coordinates recover the original slope over every overfield. -/
theorem fixed_point_iff (K : Type*) [Field K] [Algebra ℚ K] (d e : ℤ) (r w : K)
    (hr : r^2=algebraMap ℚ K d) (hw : w^2=algebraMap ℚ K e) (x y : ℚ) :
    (e:ℚ)*y^2=sextic d x ↔
    let Z:=r*algebraMap ℚ K x
    let V:=w*algebraMap ℚ K y
    V^2=(1-Z^2)*(2401*Z^2-2400)*(375-343*Z^2) := by
  dsimp only
  rw [mul_pow,mul_pow,hr,hw]
  have eq : algebraMap ℚ K (sextic d x)=
      (1-algebraMap ℚ K d*(algebraMap ℚ K x)^2)*
      (2401*(algebraMap ℚ K d*(algebraMap ℚ K x)^2)-2400)*
      (375-343*(algebraMap ℚ K d*(algebraMap ℚ K x)^2)) := by
    simp only [sextic,cubic,map_mul,map_sub,map_pow,map_one,map_ofNat]
  rw [←eq,←map_pow,←map_mul,(algebraMap ℚ K).injective.eq_iff]

open Polynomial
local notation "Ω" => AlgebraicClosure ℚ

private theorem root_degree {r : Ω} {d : ℤ} (hr : r^2=(d:Ω)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({r} : Set Ω)) ≤ 2 := by
  let P : ℚ[X] := X^2-C (d:ℚ)
  have m : P.Monic := monic_X_pow_sub_C _ (by decide)
  have z : aeval r P=0 := by simp [P,hr]
  rw [IntermediateField.adjoin.finrank (show IsIntegral ℚ r from ⟨P,m,z⟩)]
  exact (natDegree_le_natDegree (minpoly.min ℚ r m z)).trans_eq natDegree_X_pow_sub_C

/-- The actual compositum of the two root fields is a finite extension of degree at most four.
Its elements Z,V lie on a fixed curve over Q, with the rational slope recovered as 1/(1-Z²). -/
theorem fixed_curve_lift {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    ∃ r w : Ω, r^2=(D A B:Ω) ∧ w^2=(E A B:Ω) ∧
      let L:=IntermediateField.adjoin ℚ ({r,w} : Set Ω)
      FiniteDimensional ℚ L ∧ Module.finrank ℚ L≤4 ∧
      ∃ z v : L, v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) ∧
        (1-z^2)⁻¹=algebraMap ℚ L ((A:ℚ)/B) := by
  obtain ⟨sd,se,x,y,nx,ny,pt,back⟩:=forward off
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq (D A B:Ω) (by decide : 0<2)
  obtain ⟨w,hw⟩:=IsAlgClosed.exists_pow_nat_eq (E A B:Ω) (by decide : 0<2)
  let L:=IntermediateField.adjoin ℚ ({r,w} : Set Ω)
  let rL : L:=⟨r,IntermediateField.mem_adjoin_pair_left ℚ r w⟩
  let wL : L:=⟨w,IntermediateField.mem_adjoin_pair_right ℚ r w⟩
  have hrL : rL^2=algebraMap ℚ L (D A B) := Subtype.ext (by simpa using hr)
  have hwL : wL^2=algebraMap ℚ L (E A B) := Subtype.ext (by simpa using hw)
  have degree : Module.finrank ℚ L≤4 := by
    let R:=IntermediateField.adjoin ℚ ({r}:Set Ω)
    let W:=IntermediateField.adjoin ℚ ({w}:Set Ω)
    have h : R ⊔ W=L := by
      dsimp [L,R,W]
      rw [←IntermediateField.adjoin_union,Set.singleton_union]
    have eq:=congrArg (fun F : IntermediateField ℚ Ω => Module.finrank ℚ F) h
    exact eq ▸ (IntermediateField.finrank_sup_le R W).trans (Nat.mul_le_mul (root_degree hr) (root_degree hw))
  refine ⟨r,w,hr,hw,IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral r) (Algebra.IsIntegral.isIntegral w),degree,
    rL*algebraMap ℚ L x,wL*algebraMap ℚ L y,(fixed_point_iff L _ _ rL wL hrL hwL x y).mp pt,?_⟩
  rw [←back]
  simp only [parameter,map_inv₀,map_sub,map_one,map_mul,map_pow,mul_pow,hrL]
  rfl


end
end Sun28.FiveDescent
#print axioms Sun28.FiveDescent.fixed_point_iff

#print axioms Sun28.FiveDescent.fixed_curve_lift
