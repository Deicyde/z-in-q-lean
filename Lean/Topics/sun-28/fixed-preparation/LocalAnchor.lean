import FixedAnchor
import DyadicTruncation
import ZInQKernel.Assembly.Local.DeepMultiples

/-! The factorial anchor lies in the required formal layers at every preparation prime. -/
namespace Sun28.FixedPreparation
open WeierstrassCurve.Affine ZInQ ZInQ.Mult ZInQ.Assembly ZInQ.Size Sun28.Scalar
noncomputable section

private theorem unit_scale {π : Zs} (hπ : Prime π) : vP π hπ (epsilon^2)=0 := by
  have e : vP π hπ epsilon=0 := by
    rw [vP_apply hπ epsilon_ne_zero,←toK0_epsUnit,vp_unit hπ]; rfl
  rw [(vP π hπ).map_pow,e]; simp

theorem anchor_dyadic : Vge vS 4 (parameter (anchor • paperGenerator sqrt2_sq)) := by
  have hp : Vge vS 1 ((2:ℤ):K0) := by
    change (1:WithTop ℤ)≤vS ((2:ℕ):K0)
    rw [vS_two_eq]; norm_num
  have twice := zsmul_mem_formalFilt_succ vS_genA_nonneg hp (by decide : (1:ℤ)≤3) genP0_mem_formalFilt_three
  obtain ⟨k,hk⟩ := (show (2:ℤ)∣64 by decide).trans anchor_64
  have all : anchor • genP0 ∈ Ek sqrt2Z prime_sqrt2Z 4 := by
    rw [hk,mul_comm,mul_smul]
    exact (Ek sqrt2Z prime_sqrt2Z 4).zsmul_mem twice k
  rw [parameter_on_multiple]
  exact (show Vge vS 4 (zCoord (A:=-genD^2) (anchor • genP0)) from all.2).div_unit (unit_scale prime_sqrt2Z)

/-- For π above q in the real quadratic field, the residue degree is one or two. -/
theorem residue_card {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) {π : Zs}
    (hπ : Prime π) (above : π ∣ (p:Zs)) :
    Nat.card (Zs ⧸ Ideal.span {π})=p ∨ Nat.card (Zs ⧸ Ideal.span {π})=p^2 := by
  by_cases sq2 : IsSquare (2:ZMod p)
  · obtain ⟨u,hu⟩ := sq2
    let r : ℤ := u.val
    have e : (r:ZMod p)^2=2 := by
      simp only [r,Int.cast_natCast,ZMod.natCast_zmod_val,sq]; exact hu.symm
    obtain ⟨_,_,_,_,_,all⟩ := primeR_split odd e
    have prime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
    left
    rcases all _ prime (Ideal.mem_span_singleton.mpr above) with h|h
    · rw [h,Nat.card_congr (quotPrimeREquiv e).toEquiv,Nat.card_zmod]
    · rw [h,Nat.card_congr (quotPrimeREquiv (neg_sq_eq e)).toEquiv,Nat.card_zmod]
  · right
    obtain ⟨_,card,_,_⟩ := primeP_inert sq2
    rw [Ideal.span_singleton_eq_span_singleton.mpr (hπ.associated_of_dvd
      (prime_natCast_of_not_isSquare sq2) above)]
    exact card

/-- A good reduced short curve has even cardinality: the origin of the affine chart has order two. -/
theorem even_card_good {k : Type*} [Field k] [DecidableEq k] {b : k} (hb : b≠0) :
    2∣Nat.card (shortCurve b).toAffine.Point := by
  have hs : (shortCurve b).toAffine.Nonsingular 0 0 := by
    simpa using hb
  let T := Point.some 0 0 hs
  have two : 2 • T=0 := (two_nsmul_some_eq_zero_iff hs).mpr (by simp)
  have e : addOrderOf T=2 := addOrderOf_eq_prime two (Point.some_ne_zero hs)
  rw [←e]; exact addOrderOf_dvd_natCard T

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.anchor_dyadic
#print axioms Sun28.FixedPreparation.residue_card
#print axioms Sun28.FixedPreparation.even_card_good
