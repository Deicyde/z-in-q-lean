import GaloisOrbitMinus
import FixedBranch
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! Rationalization of the source Galois eigenspace and its application to rank.
The source is A : Y² = X³+4X. The target is E : y² = x³−x. -/
namespace ZInQBlueprint.TYZ.Specialization
open TensorProduct TraceAction
open scoped TensorProduct nonZeroDivisors
noncomputable section
attribute [local instance] Classical.decEq

/-- Equality to zero after extending scalars from ℤ to ℚ is exactly torsion. -/
theorem one_tmul_eq_zero_iff {G : Type*} [AddCommGroup G] (P : G) :
    (1:ℚ) ⊗ₜ[ℤ] P = 0 ↔ IsOfFinAddOrder P := by
  change (TensorProduct.mk ℤ ℚ G 1) P = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff ℤ⁰ (TensorProduct.mk ℤ ℚ G 1),
    isOfFinAddOrder_iff_zsmul_eq_zero]
  simp [Submonoid.smul_def, mem_nonZeroDivisors_iff_ne_zero]

def signedSource (n : ℕ) (σ : Gal) (P : A) : A :=
  if σ (Rank.sqrtMinus n) = Rank.sqrtMinus n then P else -P

/-- The class of P in A(Qbar) tensored with Q transforms by the quadratic character. -/
def RationalMinus (n : ℕ) (P : A) : Prop :=
  ∀ σ : Gal, (1:ℚ) ⊗ₜ[ℤ] sourceAction σ P = (1:ℚ) ⊗ₜ[ℤ] signedSource n σ P

theorem rationalMinus_iff (n : ℕ) (P : A) :
    RationalMinus n P ↔ ∀ σ : Gal, IsOfFinAddOrder (sourceAction σ P - signedSource n σ P) := by
  simp only [RationalMinus, ← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, sub_eq_zero]

/-- A rational isogeny sends the character relation in the tensor product
to the same character relation modulo torsion on the target. -/
theorem rationalMinus_image_double {n : ℕ} {P : A} (h : RationalMinus n P) :
    MinusModuloTorsion n (tyzIsogeny ((2:ℕ) • P)) := by
  intro σ
  have hT := (rationalMinus_iff n P).mp h σ
  obtain ⟨m,hm,hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hT
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨m,hm,?_⟩
  have he : targetAction σ (tyzIsogeny ((2:ℕ) • P)) - signedTarget n σ (tyzIsogeny ((2:ℕ) • P)) =
      tyzIsogeny ((2:ℕ) • (sourceAction σ P - signedSource n σ P)) := by
    rw [isogeny_galois,map_nsmul, signedSource,signedTarget]
    split_ifs <;> simp only [nsmul_sub, two_nsmul, map_sub, map_add, map_neg, neg_add_rev]
  rw [he, ←map_nsmul, smul_comm m (2:ℕ),hkill,nsmul_zero,map_zero]

/-- The image of an infinite-order genus point has some infinite-order multiple
over the quadratic field in the negative eigenspace. -/
theorem antiPoint_of_rationalMinus {n : ℕ} (hn : 0 < n) {P : A}
    (hi : Rank.InfiniteOrder P) (h : RationalMinus n P) : Rank.AntiPoint n :=
  antiPoint_of_minusModuloTorsion hn
    (Rank.image_double_infinite tyzIsogeny tyzIsogeny_kernel_two P hi) (rationalMinus_image_double h)

/-- The odd class-group row is the only case in which the trace and torsion
inputs are needed. Anti-invariance after tensoring suffices on its representative. -/
theorem rank_of_rationalMinus (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (hf : TraceFields (S.recursion L eps) S.extended)
    (pointwise : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 →
      (∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n) ∧
      (∀ Y : pointsOver (genusCompositum S.extended n), IsOfFinAddOrder Y.val →
        onePlusI (onePlusI (onePlusI Y.val)) = 0) ∧ RationalMinus n (representative (S.recursion L eps) n)) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro n hn hs ho
  obtain ⟨⟨σ,hσ⟩,hT,hm⟩ := pointwise n hn hs ho
  have hb := (row_coefficient h1 hc hs hn).trans ho
  have hodd : Odd (traceCoefficient L n) := by
    by_contra hz
    exact zero_ne_one ((Int.not_odd_iff_even.mp hz).intCast_zmod_two.symm.trans hb)
  let P := representative (S.recursion L eps) n
  have hmem : P ∈ pointsOver (genusCompositum S.extended n) := representative_mem hf n hs (Or.inl hn)
  apply antiPoint_of_rationalMinus (by omega : 0 < n) (P := P) _ hm
  apply infinite_of_odd hσ (Or.inl hn) _ hodd
  intro m hpos hkill
  exact gaussian_torsion (hT ⟨P,hmem⟩ (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m,hpos,hkill⟩))

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.one_tmul_eq_zero_iff
#print axioms ZInQBlueprint.TYZ.Specialization.rationalMinus_iff
#print axioms ZInQBlueprint.TYZ.Specialization.rationalMinus_image_double
#print axioms ZInQBlueprint.TYZ.Specialization.antiPoint_of_rationalMinus
#print axioms ZInQBlueprint.TYZ.Specialization.rank_of_rationalMinus
