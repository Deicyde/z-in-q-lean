import LocalAnchor

/-! Simultaneous fixed local exponents, including the inert place over 19. -/
namespace Sun28.FixedPreparation
open WeierstrassCurve WeierstrassCurve.Affine ZInQ ZInQ.Mult ZInQ.Assembly ZInQ.Size Sun28.Scalar
noncomputable section

private theorem enter_two {q n : ℕ} {π : Zs} (hπ : Prime π) (above : π∣(q:Zs))
    (divides : q*n∣anchor.natAbs)
    (first : ∀ k : ℤ, (k*(n:ℤ)) • genP0 ∈ E1sub hπ (vge_neg_genD_sq _ hπ)) :
    anchor • genP0 ∈ Ek π hπ 2 := by
  obtain ⟨k,hk⟩ := divides
  have id : anchor=(q:ℤ)*((k:ℤ)*(n:ℤ)) := by
    change ((Nat.factorial 576:ℕ):ℤ)=_
    change Nat.factorial 576=q*n*k at hk
    rw [hk]; push_cast; ring
  have init : ((k:ℤ)*(n:ℤ)) • genP0∈Ek π hπ 1 :=
    (mem_formalNbhd_iff (vP_genA_nonneg π hπ) _).mpr ((inE1_iff_mem_W1 hπ _).mp (first k))
  rw [id,mul_smul]
  exact zsmul_mem_formalFilt_succ (vP_genA_nonneg π hπ) (vge_natCast_of_dvd hπ above) (by decide : (1:ℤ)≤1) init

/-- Over every odd rational prime q ≤ 23 the explicit 576! reaches layer two.
The bad place over 7 uses nonsingular reduction of the displayed generator.
At good primes evenness of the reduction order of the whole group suffices. -/
theorem anchor_odd {q : ℕ} [hq : Fact q.Prime] (odd : q≠2) (small : q≤23)
    {π : Zs} (hπ : Prime π) (above : π∣(q:Zs)) :
    anchor • genP0 ∈ Ek π hπ 2 := by
  classical
  have hr := residue_card odd hπ above
  have nz : Nat.card (Zs ⧸ Ideal.span {π})≠0 := by
    rcases hr with h|h
    · rw [h]; exact hq.out.ne_zero
    · rw [h]; exact pow_ne_zero _ hq.out.ne_zero
  have h2 := not_dvd_two_of_dvd_odd odd hπ above
  by_cases bad : Associated π genDZ
  · obtain ⟨n,positive,bound,first⟩ := exists_order_at_prime hπ h2 nz
    rw [Ideal.span_singleton_eq_span_singleton.mpr bad,natCard_quot_genDZ] at bound
    exact enter_two hπ above (factorial_local_order hq.out.pos small positive (by omega)) first
  · let _ := span_isMaximal hπ
    let k := Zs ⧸ Ideal.span {π}
    let _ : Field k := Ideal.Quotient.field _
    have : Finite k := Nat.finite_of_card_ne_zero nz
    let _ : Fintype k := Fintype.ofFinite k
    let ρ : Zs →+* k := Ideal.Quotient.mk _
    have ker : ∀ a, ρ a=0 ↔ π∣a := quotient_mk_eq_zero_iff π
    let b := resK π ρ (-genD^2)
    have good : b≠0 := resK_genA_ne_zero hπ ρ ker bad
    let R := redK π ρ (-genD^2) b genP0
    have smooth : genP0 ∈ E0sub hπ ρ ker (vge_neg_genD_sq _ hπ) (hAb:=rfl) h2 := by
      rw [E0_eq_top_of_ne_d hπ _ ker h2 bad]; exact AddSubgroup.mem_top _
    have first := zsmul_addOrderOf_mem_E1 hπ ρ ker (vge_neg_genD_sq _ hπ) rfl h2 smooth
    have count := card_points_le b
    rw [←Nat.card_eq_fintype_card] at count
    have cap : Nat.card k≤529 := by
      rcases hr with h|h
      · change Nat.card k=q at h
        omega
      · change Nat.card k=q^2 at h
        exact h.le.trans (Nat.pow_le_pow_left small 2)
    obtain ⟨t,ht⟩ := even_card_good good
    have gt : 0<Nat.card (shortCurve b).toAffine.Point := Nat.card_pos
    have kills := (Nat.mul_dvd_mul_left q (addOrderOf_dvd_natCard R)).trans
      (ht ▸ factorial_even_group hq.out.pos small (by omega) (by omega))
    exact enter_two hπ above kills first

/-- The actual Sun generator has integral uniformizer order at least two at all odd preparation places. -/
theorem paper_anchor_odd {q : ℕ} [Fact q.Prime] (odd : q≠2) (small : q≤23)
    {π : Zs} (hπ : Prime π) (above : π∣(q:Zs)) :
    Vge (vP π hπ) 2 (parameter (anchor • paperGenerator sqrt2_sq)) := by
  rw [parameter_on_multiple]
  have depth := (mem_Ek_iff hπ 2 _).mp (anchor_odd odd small hπ above) |>.2
  have unit : vP π hπ epsilon=0 := by
    rw [vP_apply hπ epsilon_ne_zero,←toK0_epsUnit,vp_unit hπ]; rfl
  exact (show Vge (vP π hπ) 2 _ from depth).div_unit (by rw [(vP π hπ).map_pow,unit]; simp)

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.anchor_odd
#print axioms Sun28.FixedPreparation.paper_anchor_odd
