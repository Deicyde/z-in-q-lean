import SignedImages
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Sun28.ScalarRankZero
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
noncomputable section

def curve (A B:ℤ) : WeierstrassCurve ℚ := ⟨0,A,0,B,0⟩

/-- Cremona, Algorithms for Modular Elliptic Curves, §§3.3 and 3.6, equation (3.6.2).
The natural rank witness records the finite rank in Mordell's theorem. -/
def TwoIsogenyRank : Prop := ∀ A B:ℤ, B≠0 → A^2-4*B≠0 → ∃ r:ℕ,
  Module.rank ℤ (curve A B).toAffine.Point = (r:Cardinal) ∧
  2^(r+2) = (images A B).card*(images (-2*A) (A^2-4*B)).card

/-- Rational point at infinity and the actual affine point equation in characteristic p. -/
abbrev ResiduePoints (p:ℕ) (A B:ℤ) := Option {z:ZMod p × ZMod p //
  z.2^2=z.1*(z.1^2+(A:ZMod p)*z.1+(B:ZMod p))}

/-- Cremona §3.3, p.70. Over Q the entire rational torsion group injects at an odd good prime. -/
def OddGoodReduction : Prop := ∀ (A B:ℤ) (p:ℕ), p.Prime → p≠2 →
  ¬(p:ℤ)∣16*B^2*(A^2-4*B) →
  Nonempty ({P:(curve A B).toAffine.Point // IsOfFinAddOrder P} ↪ ResiduePoints p A B)

def m (j:Fin 2) : ℤ := ![4,64] j
def n (j:Fin 2) : ℤ := ![6,439] j
def a (j:Fin 2) : ℤ := m j+n j
def b (j:Fin 2) : ℤ := m j*n j
abbrev Points (j:Fin 2) := (curve (a j) (b j)).toAffine.Point

theorem rank_zero (descent:TwoIsogenyRank) (j:Fin 2) : Module.rank ℤ (Points j)=0 := by
  obtain ⟨r,h,e⟩:=descent (a j) (b j) (by fin_cases j <;> decide) (by fin_cases j <;> decide)
  have cap:(images (a j) (b j)).card*(images (-2*a j) (a j^2-4*b j)).card≤4 := by
    fin_cases j
    · exact image_products.1
    · exact image_products.2
  have rp:r=0 := by
    by_contra! hr
    have big:(2:ℕ)^3≤2^(r+2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simpa [rp] using h

theorem all_torsion (descent:TwoIsogenyRank) (j:Fin 2) (P:Points j) : IsOfFinAddOrder P := by
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr (rank_eq_zero_iff.mp (rank_zero descent j) P)

private def finiteEncoding (j:Fin 2) : Equiv (ResiduePoints 7 (a j) (b j)) (Fin 4) := by

  apply Fintype.equivFinOfCardEq
  fin_cases j <;> decide

theorem embeds_in_four (descent:TwoIsogenyRank) (reduction:OddGoodReduction) (j:Fin 2) :
    Nonempty (Points j ↪ Fin 4) := by
  obtain ⟨inj⟩:=reduction (a j) (b j) 7 (by decide) (by decide) (by fin_cases j <;> decide)
  let includePoint : Points j ↪ {P:Points j // IsOfFinAddOrder P} :=
    ⟨fun P=>⟨P,all_torsion descent j P⟩,fun _ _ h=>congrArg Subtype.val h⟩
  exact ⟨(includePoint.trans inj).trans (finiteEncoding j).toEmbedding⟩

end
end Sun28.ScalarRankZero
#print axioms Sun28.ScalarRankZero.rank_zero
#print axioms Sun28.ScalarRankZero.all_torsion
#print axioms Sun28.ScalarRankZero.embeds_in_four
