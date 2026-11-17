import GenusRecursion

/-! Only the field of the chosen odd row is needed for the torsion argument. -/
namespace ZInQBlueprint.TYZ.Specialization
open TensorProduct TraceAction
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.decEq

/-- All primitive traces used on this odd row belong to a single field. -/
def DivisorTracesOver (D : RecursionData) (N : ℕ) (F : SubfieldQ) : Prop :=
  ∀ e, e ∣ N → (e%8=5 ∨ e%8=7) → D.trace e ∈ pointsOver F

/-- The primitive trace field conditions of TYZ imply the row-local condition. -/
theorem divisorTracesOver_of_traceFields {D : RecursionData} {H : ℕ → SubfieldQ} {N : ℕ}
    (h : TraceFields D H) (hn : Squarefree N) (hN : 0 < N) :
    DivisorTracesOver D N (genusCompositum H N) := by
  intro e he hr
  rcases hr with h5 | h7
  · exact pointsOver_mono (classField_le_compositum (Nat.mem_divisors.mpr ⟨he,hN.ne'⟩) (Or.inl h5) H)
      (h.fiveSix e (hn.squarefree_of_dvd he) (Or.inl h5))
  · exact pointsOver_mono (le_trans (show radicalField e ≤ genusCompositum H e from le_sup_left)
      (compositum_mono he hN.ne' H)) (h.seven e (hn.squarefree_of_dvd he) h7)

/-- Closure of the single field under complex multiplication places every
divisor representative in it. Only the primitive genus sums enter the hypotheses. -/
theorem representative_mem_divisorField {D : RecursionData} {N : ℕ} {F : SubfieldQ}
    (hi : Rank.sqrtMinus 1 ∈ F) (hz : DivisorTracesOver D N F) (e : ℕ)
    (he : e ∣ N) (hr : e%8=5 ∨ e%8=7) : representative D e ∈ pointsOver F := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [representative_eq]
    apply (pointsOver F).sub_mem (hz e he hr)
    apply (pointsOver F).sum_mem
    intro t ht
    have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp ht).1).1
    apply (pointsOver F).zsmul_mem
    apply GaussianUnit.act_mem _ hi
    exact ih (e/t) (factor_lt ht) ((Nat.div_dvd_of_dvd hd).trans he) (cofactor_odd_class ht hr)

/-- Geometry at one odd class-group row. Both the field and the choice of
Galois lift are local to that row. -/
structure OddRowTraces (D : RecursionData) (n : ℕ) : Prop where
  localLaw : ∃ σ : Gal, LocalTraceLaw D σ n
  field : ∃ F : SubfieldQ, Rank.sqrtMinus 1 ∈ F ∧ DivisorTracesOver D n F ∧
    ∀ Y : pointsOver F, IsOfFinAddOrder Y.val → onePlusI (onePlusI (onePlusI Y.val)) = 0
  characters : ∃ v : ∀ e : ℕ, ℚ ⊗[ℤ] ↥(minusSource e),
    GenusExpansion D (fun e => minusInclusion e (v e)) n

/-- Conditional rank, with every geometric hypothesis restricted to an odd
class-group row and to the residue classes of the divisors actually used. -/
theorem rank_of_divisor_traces (D : RecursionData)
    (h1 : D.L 1 = 1) (hc : ClassThreePeriods D.L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 → OddRowTraces D n) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro n hn hs ho
  obtain ⟨⟨σ,hσ⟩,⟨F,hi,hz,ht⟩,⟨v,hv⟩⟩ := rows n hn hs ho
  have hb := (row_coefficient h1 hc hs hn).trans ho
  have hodd : Odd (traceCoefficient D.L n) := by
    by_contra h
    exact zero_ne_one ((Int.not_odd_iff_even.mp h).intCast_zmod_two.symm.trans hb)
  have hmem := representative_mem_divisorField hi hz n dvd_rfl (Or.inl hn)
  apply antiPoint_of_represents (by omega : 0 < n) _ (represents_of_character_expansion v hv (Or.inl hn))
  apply infinite_of_odd hσ (Or.inl hn) _ hodd
  intro m hm hkill
  exact gaussian_torsion (ht ⟨representative D n,hmem⟩ (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m,hm,hkill⟩))

/-- The fixed polynomial from divisor-local conditions on the specific CM sums.
No residue-six primitive trace occurs in the rank input. -/
theorem frozen_of_fixed_periods_and_divisor_traces (hp : ThetaPeriod.HasFixedPeriods)
    (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit) (h1 : L 1 = 1)
    (hc : ClassThreePeriods L)
    (rows : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 →
      OddRowTraces (S.recursion L eps) n) : ZInQ.FrozenTarget :=
  HeightBudget.frozen_of_remaining_and_class_rank
    (ThetaPeriod.remaining_of_labelledPeriods (ThetaPeriod.labelledPeriods_of_fixedPeriods hp))
    (rank_of_divisor_traces (S.recursion L eps) h1 hc rows)

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.divisorTracesOver_of_traceFields
#print axioms ZInQBlueprint.TYZ.Specialization.representative_mem_divisorField
#print axioms ZInQBlueprint.TYZ.Specialization.rank_of_divisor_traces
#print axioms ZInQBlueprint.TYZ.Specialization.frozen_of_fixed_periods_and_divisor_traces
