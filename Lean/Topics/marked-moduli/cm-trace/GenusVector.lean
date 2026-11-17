import RationalTraceRank

/-! The first assertion of TYZ Theorem 3.5 in the rationalized group. The
subgroup is defined by the action of Gal(Qbar/Q) on the actual source curve. -/
namespace ZInQBlueprint.TYZ.Specialization
open TensorProduct TraceAction
open scoped TensorProduct nonZeroDivisors
noncomputable section
attribute [local instance] Classical.decEq

/-- Source points defined over Q(sqrt(-n)) on which conjugation acts as −1. -/
def minusSource (n : ℕ) : AddSubgroup A where
  carrier := {P | ∀ σ : Gal, sourceAction σ P = signedSource n σ P}
  zero_mem' := by intro σ; simp [signedSource]
  add_mem' := by
    intro P Q hP hQ σ
    rw [map_add,hP σ,hQ σ]
    unfold signedSource
    split_ifs <;> simp [add_comm]
  neg_mem' := by
    intro P hP σ
    rw [map_neg,hP σ]
    unfold signedSource
    split_ifs <;> rfl

/-- Inclusion of the quadratic minus subgroup after applying Q ⊗_ℤ −. -/
def minusInclusion (n : ℕ) : (ℚ ⊗[ℤ] ↥(minusSource n)) →ₗ[ℤ] (ℚ ⊗[ℤ] A) :=
  (minusSource n).subtype.toIntLinearMap.lTensor ℚ

/-- Every vector coming from the rationalized quadratic minus subgroup
satisfies the Galois character equation for the recursive point it represents. -/
theorem rationalMinus_of_represents {n : ℕ} {P : A}
    (h : (1:ℚ) ⊗ₜ[ℤ] P ∈ LinearMap.range (minusInclusion n)) : RationalMinus n P := by
  obtain ⟨v,hv⟩ := h
  intro σ
  let g : (ℚ ⊗[ℤ] A) →ₗ[ℤ] (ℚ ⊗[ℤ] A) := (sourceAction σ).toIntLinearMap.lTensor ℚ
  have action (w : ℚ ⊗[ℤ] ↥(minusSource n)) :
      g (minusInclusion n w) = if σ (Rank.sqrtMinus n) = Rank.sqrtMinus n
        then minusInclusion n w else -minusInclusion n w := by
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      change a ⊗ₜ[ℤ] (sourceAction σ (b:A)) = if _ then a ⊗ₜ[ℤ] (b:A) else -(a ⊗ₜ[ℤ] (b:A))
      rw [b.property σ]
      unfold signedSource
      split_ifs <;> simp only [TensorProduct.tmul_neg]
    | add a b ha hb =>
      rw [map_add,map_add,ha,hb]
      split_ifs <;> simp [add_comm]
  have value := action v
  rw [hv] at value
  change (1:ℚ) ⊗ₜ[ℤ] sourceAction σ P = _ at value
  rw [value]
  unfold signedSource
  split_ifs <;> simp only [TensorProduct.tmul_neg]

/-- The source interpretation of TYZ Theorem 3.5 needed by the odd rank criterion. -/
def RepresentsGenusVector (n : ℕ) (P : A) : Prop :=
  (1:ℚ) ⊗ₜ[ℤ] P ∈ LinearMap.range (minusInclusion n)

/-- Membership in the rational span of the minus subgroup is exactly the
existence of a positive multiple lying in that subgroup. -/
theorem represents_iff_multiple (n : ℕ) (P : A) :
    RepresentsGenusVector n P ↔ ∃ m : ℕ, 0 < m ∧ m • P ∈ minusSource n := by
  constructor
  · rintro ⟨v,hv⟩
    let T := minusSource n
    let ι := TensorProduct.mk ℤ ℚ (↥T) 1
    obtain ⟨⟨Q,b⟩,hQ⟩ := IsLocalizedModule.surj ℤ⁰ ι v
    let j := TensorProduct.mk ℤ ℚ A 1
    have rel := congrArg (minusInclusion n) hQ
    change minusInclusion n ((b:ℤ) • v) = j (Q:A) at rel
    rw [map_smul,hv] at rel
    change (b:ℤ) • j P = j (Q:A) at rel
    rw [← map_smul] at rel
    have hz : j ((b:ℤ) • P - (Q:A)) = 0 := by rw [map_sub,rel,sub_self]
    obtain ⟨k,hk,hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ((one_tmul_eq_zero_iff _).mp hz)
    have he : k • ((b:ℤ) • P) = k • (Q:A) := sub_eq_zero.mp ((nsmul_sub _ _ _).symm.trans hkill)
    have mem : (k:ℤ) • (b:ℤ) • P ∈ T := by
      rw [natCast_zsmul,he]
      exact T.nsmul_mem Q.property k
    rw [← mul_zsmul] at mem
    let z : ℤ := k * (b:ℤ)
    have zne : z ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') (nonZeroDivisors.coe_ne_zero b)
    refine ⟨z.natAbs,Int.natAbs_pos.mpr zne,?_⟩
    change z • P ∈ T at mem
    rcases Int.natAbs_eq z with h | h
    · rwa [h,natCast_zsmul] at mem
    · rwa [h,neg_zsmul,natCast_zsmul,T.neg_mem_iff] at mem
  · rintro ⟨m,hm,hP⟩
    let Q : minusSource n := ⟨m • P,hP⟩
    refine ⟨((m:ℚ)⁻¹) ⊗ₜ[ℤ] Q,?_⟩
    change ((m:ℚ)⁻¹) ⊗ₜ[ℤ] (m • P) = _
    rw [← TensorProduct.smul_tmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hm.ne')]

/-- A representative of a nonzero minus vector gives rational anti-invariant
coordinates after clearing one denominator and applying the rational isogeny. -/
theorem antiPoint_of_represents {n : ℕ} (hn : 0 < n) {P : A}
    (hi : Rank.InfiniteOrder P) (hv : RepresentsGenusVector n P) : Rank.AntiPoint n := by
  obtain ⟨m,hm,hP⟩ := (represents_iff_multiple n P).mp hv
  let Q := m • P
  have hinf : Rank.InfiniteOrder Q := by
    intro k hk hz
    exact hi (m*k) (Nat.mul_pos hm hk) ((mul_nsmul _ _ _).trans hz)
  have hImage := Rank.image_double_infinite tyzIsogeny tyzIsogeny_kernel_two Q hinf
  have hM : GaloisMinus n (tyzIsogeny ((2:ℕ) • Q)) := by
    intro σ
    have hs : sourceAction σ Q = signedSource n σ Q := hP σ
    rw [isogeny_galois,map_nsmul,hs]
    unfold signedSource
    split_ifs <;> simp only [two_nsmul,map_add,map_neg,neg_add_rev]
  obtain hzero | ⟨x,y,h,he⟩ := (minus_iff_coordinates hn _).mp hM
  · exact False.elim (hImage 1 (by decide) (by simpa using hzero))
  · exact ⟨x,y,h,he ▸ hImage⟩

/-- The rational witness may be any positive multiple of the recursively
constructed representative. Only odd rows of the public parity condition matter. -/
theorem rank_of_genusVectors (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (hf : TraceFields (S.recursion L eps) S.extended)
    (pointwise : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 →
      (∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n) ∧
      (∀ Y : pointsOver (genusCompositum S.extended n), IsOfFinAddOrder Y.val →
        onePlusI (onePlusI (onePlusI Y.val)) = 0) ∧
      RepresentsGenusVector n (representative (S.recursion L eps) n)) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro n hn hs ho
  obtain ⟨⟨σ,hσ⟩,hT,hv⟩ := pointwise n hn hs ho
  have hb := (row_coefficient h1 hc hs hn).trans ho
  have hodd : Odd (traceCoefficient L n) := by
    by_contra hz
    exact zero_ne_one ((Int.not_odd_iff_even.mp hz).intCast_zmod_two.symm.trans hb)
  let P := representative (S.recursion L eps) n
  have hmem : P ∈ pointsOver (genusCompositum S.extended n) := representative_mem hf n hs (Or.inl hn)
  apply antiPoint_of_represents (by omega : 0 < n) (P := P) _ hv
  apply infinite_of_odd hσ (Or.inl hn) _ hodd
  intro m hpos hkill
  exact gaussian_torsion (hT ⟨P,hmem⟩ (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m,hpos,hkill⟩))

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.minusSource
#print axioms ZInQBlueprint.TYZ.Specialization.minusInclusion
#print axioms ZInQBlueprint.TYZ.Specialization.rationalMinus_of_represents
#print axioms ZInQBlueprint.TYZ.Specialization.represents_iff_multiple
#print axioms ZInQBlueprint.TYZ.Specialization.rank_of_genusVectors
#print axioms ZInQBlueprint.TYZ.Specialization.antiPoint_of_represents
