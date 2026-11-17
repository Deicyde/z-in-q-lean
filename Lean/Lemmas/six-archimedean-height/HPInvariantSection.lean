import HPSexticDiscriminant
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RingTheory.Derivation.Basic

/-! The coordinate change and the invariant twentieth tensor power of the
determinant of the two regular differentials. -/
open Polynomial
namespace ZInQBlueprint.ArchimedeanHeight
open OddModel ThetaPeriod BinaryCover
noncomputable section

/-- The chain rule in any differential module over a characteristic-zero
function field. In particular it applies to the universal Kähler derivation. -/
theorem restricted_differentials {F M : Type*} [Field F] [Algebra ℂ F]
    [AddCommGroup M] [Module F M] [Module ℂ M] [IsScalarTower ℂ F M] [CharZero F]
    (D : Derivation ℂ F M) (p s : ℂ) (x y : F) (hx : x ≠ algebraMap ℂ F p)
    (hs : s ≠ 0) (hy : y ≠ 0) :
    let r := algebraMap ℂ F p
    let t := algebraMap ℂ F s
    let z := (x-r)⁻¹
    let w := y/(t*(x-r)^3)
    let ω₁ := (2*y)⁻¹ • D x
    let ω₂ := (x/(2*y)) • D x
    (2*w)⁻¹ • D z = (t*r) • ω₁ + (-t) • ω₂ ∧
      (z/(2*w)) • D z = (-t) • ω₁ := by
  dsimp only
  rw [D.leibniz_inv,map_sub,D.map_algebraMap,sub_zero]
  simp only [smul_smul,← add_smul]
  have ht : algebraMap ℂ F s ≠ 0 := (map_ne_zero (algebraMap ℂ F)).mpr hs
  constructor <;> apply congrArg (fun c : F => c • D x) <;>
    field_simp [sub_ne_zero.mpr hx,ht,hy]
  ring

private def pairWedge {M : Type*} [AddCommGroup M] [Module ℂ M] (x y : M) :=
  exteriorPower.ιMulti ℂ 2 ![x,y]

private theorem wedge_swap {M : Type*} [AddCommGroup M] [Module ℂ M] (x y : M) :
    pairWedge y x = -pairWedge x y := by
  let T := exteriorPower.ιMulti ℂ 2 (M:=M)
  have vec : (![x,y] : Fin 2 → M) ∘ Equiv.swap 0 1 = ![y,x] := by
    funext i; fin_cases i <;> simp
  change T ![y,x] = -T ![x,y]
  rw [← vec]
  exact T.map_swap _ (by decide : (0:Fin 2) ≠ 1)

private theorem wedge_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (x y : M) (c : ℂ) :
    pairWedge (c • x) y = c • pairWedge x y :=
  (exteriorPower.ιMulti ℂ 2).map_vecCons_smul _ _ _

private theorem wedge_change {M : Type*} [AddCommGroup M] [Module ℂ M] (x y : M) (p s : ℂ) :
    pairWedge ((s*p) • x + (-s) • y) ((-s) • x) = (-s^2) • pairWedge x y := by
  have zero : pairWedge x x = 0 :=
    (exteriorPower.ιMulti ℂ 2).map_eq_zero_of_eq _ (i:=0) (j:=1) rfl (by decide)
  have second (a b : M) (t : ℂ) : pairWedge a (t • b) = t • pairWedge a b := by
    rw [wedge_swap (t • b) a,wedge_smul,wedge_swap a b,smul_neg,neg_neg]
  rw [second]
  change (-s) • (exteriorPower.ιMulti ℂ 2 ![(s*p) • x+(-s) • y,x]) = _
  rw [AlternatingMap.map_vecCons_add,AlternatingMap.map_vecCons_smul,
    AlternatingMap.map_vecCons_smul]
  change (-s) • ((s*p) • pairWedge x x+(-s) • pairWedge y x) = _
  rw [zero,smul_zero,zero_add,wedge_swap x y]
  simp only [smul_neg,neg_neg,smul_smul,neg_mul,sq,neg_smul]
  exact (neg_smul _ _).symm

/-- HP (4.4) in the twentieth tensor power of the exterior square of the
space of differentials. The scalar on the sextic side is the rational discriminant. -/
theorem invariant_tensor {M : Type*} [AddCommGroup M] [Module ℂ M] (x y : M)
    (f : ℚ[X]) (hd : f.natDegree=6) (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, aeval (r i) f = 0) (s : ℂ) (hs : s^2=ordinateFactor (f.leadingCoeff : ℂ) r) :
    ((2:ℂ)^8*(quintic r).discr)^2 • PiTensorProduct.tprod ℂ
       (fun _ : Fin 20 => exteriorPower.ιMulti ℂ 2
         ![(s*r (Fin.last 5)) • x + (-s) • y, (-s) • x]) =
    ((2:ℂ)^8*(f.discr:ℂ))^2 • PiTensorProduct.tprod ℂ
       (fun _ : Fin 20 => exteriorPower.ιMulti ℂ 2 ![x,y]) := by
  change _ • PiTensorProduct.tprod ℂ
      (fun _ : Fin 20 => pairWedge ((s*r (Fin.last 5)) • x + (-s) • y) ((-s) • x)) =
      _ • PiTensorProduct.tprod ℂ (fun _ : Fin 20 => pairWedge x y)
  simp_rw [wedge_change]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ (fun _ : Fin 20 => -s^2)
    (fun _ : Fin 20 => pairWedge x y)]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_smul]
  rw [← sextic_discriminant f hd r hr hz s hs]
  congr 1
  ring

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.restricted_differentials
#print axioms ZInQBlueprint.ArchimedeanHeight.invariant_tensor
