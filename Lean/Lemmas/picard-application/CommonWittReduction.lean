import CommonWittField
import PicardGoodReduction

/-! Local reduction of the rational factor over a common field of definition. -/

open CategoryTheory
open ZInQBlueprint.AbelianModel
open ZInQ ZInQ.QualitativeHeight
open ZOverQ.Qualitative.LocalSupport ZOverQ.Qualitative.PicardLocalization
open ZOverQ.Qualitative.PicardConjugation ZOverQ.Qualitative.PicardDescent
open ZOverQ.Qualitative.Picard.Assembly ZOverQ.Qualitative.PicardGoodReduction

namespace ZOverQ.Qualitative.CommonWittReduction
open CommonWittField
noncomputable section

private theorem twist_ne (s : ℚ) : ((PrimitiveTwist.twist s : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast (PrimitiveTwist.positive s).ne'

/-- Localizing the common-field surjection only requires its base change for
embeddings which agree on the prescribed square root of minus three. -/
def LocalPowerMaps (p : ℕ) [Fact p.Prime] (M : Type) [Field M] [NumberField M]
    (ψ : fixedField →ₐ[ℚ] M) (t : ℚ) (ht : t ∉ contactSet) (B : GroupScheme ℚ) (n : ℕ) : Prop :=
  let s := picardParameter t
  let e : ℤ := PrimitiveTwist.twist s
  let J := familyJacobian t (e : ℚ) ht (twist_ne s) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
  ∀ (q : PicardLocal.WittRing p) (A : Finset (Fin 2)) (m : ℕ) (D : FibreData p s.num s.den e q A m),
    q^2 = -3 →
    let k := D.finiteModel.field
    letI : Finite k := D.finiteModel.finite
    letI := wittCharZero p k
    let S := WittVector p k
    let K := FractionRing S
    ∀ i : M →ₐ[ℚ] K, i (ψ ρ) = algebraMap S K D.finiteModel.rho →
      LocalPowerQuotient p k ((baseChange (i.comp ψ).toRingHom).obj J) n B

/-- One finite prime set works for every supplied DDMM fibre, with arbitrary
root labels and cluster depths. -/
theorem good_reduction_of_fibre (M : Type) [Field M] [NumberField M] [Normal ℚ M]
    (ψ : fixedField →ₐ[ℚ] M) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ 2 ∈ S ∧ 3 ∈ S ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∉ S → SplitSexticDDMM → SerreTateAt p →
      ∀ (t : ℚ) (ht : t ∉ contactSet) (B : GroupScheme ℚ), IsAbelianScheme B →
      ∀ n : ℕ, LocalPowerMaps p M ψ t ht B n →
      let s := picardParameter t
      let e : ℤ := PrimitiveTwist.twist s
      ∀ {q : PicardLocal.WittRing p} {A : Finset (Fin 2)} {m : ℕ}, q^2 = -3 →
        FibreData p s.num s.den e q A m → GoodReductionAt p B := by
  have hδ : (ψ ρ)^2 = -3 := by rw [← map_pow,rho_sq,map_neg,map_ofNat]
  obtain ⟨N,hn,h⟩ := common_marked_fibre M (ψ ρ) hδ
  let S := insert 2 (insert 3 N.natAbs.primeFactors)
  refine ⟨S,?_,by simp [S],by simp [S],?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl|hp
    · decide
    rcases Finset.mem_insert.mp hp with rfl|hp
    · decide
    exact Nat.prime_of_mem_primeFactors hp
  intro p prime away criterion st t ht B hB n maps s e q A m hq D
  have h₂ : p ≠ 2 := by rintro rfl; exact away (by simp [S])
  have h₃ : p ≠ 3 := by rintro rfl; exact away (by simp [S])
  have gt : 3 < p := by have := prime.out.two_le; omega
  have good : (N : ZMod p) ≠ 0 := by
    intro zero
    have dvd : p ∣ N.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp zero)
    exact away (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Nat.mem_primeFactors.mpr ⟨prime.out,dvd,Int.natAbs_ne_zero.mpr hn⟩)))
  obtain ⟨D',_,_,i,hi⟩ := h p good hq D
  let := D'.finiteModel.finite
  let := wittCharZero p D'.finiteModel.field
  have he : e ≠ 0 := by
    change (PrimitiveTwist.twist (picardParameter t) : ℤ) ≠ 0
    exact_mod_cast (PrimitiveTwist.positive (picardParameter t)).ne'
  exact reduction_of_fibre_power criterion p gt st hB t e ht he hq D'
    (i.comp ψ) hi n (maps q A m D' hq i hi)

/-- The cluster-condition premise of the rational-factor construction is
sufficient, with the same fixed set of primes for every rational parameter. -/
theorem good_reduction_of_clusters (M : Type) [Field M] [NumberField M] [Normal ℚ M]
    (ψ : fixedField →ₐ[ℚ] M) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ 2 ∈ S ∧ 3 ∈ S ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∉ S → SplitSexticDDMM → SerreTateAt p →
      ∀ (t : ℚ) (ht : t ∉ contactSet) (B : GroupScheme ℚ), IsAbelianScheme B →
      ∀ n : ℕ, LocalPowerMaps p M ψ t ht B n →
        ClusterCondition p (picardParameter t) → GoodReductionAt p B := by
  obtain ⟨S,primes,h₂,h₃,reduce⟩ := good_reduction_of_fibre M ψ
  refine ⟨S,primes,h₂,h₃,?_⟩
  intro p prime away criterion st t ht B hB n maps cluster
  obtain ⟨q,hq,A,m,⟨D⟩⟩ := cluster
  exact reduce p away criterion st t ht B hB n maps hq D

/-- Outside the fixed set an even branch order supplies a local DDMM fibre. -/
theorem good_reduction_outside (M : Type) [Field M] [NumberField M] [Normal ℚ M]
    (ψ : fixedField →ₐ[ℚ] M) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ 2 ∈ S ∧ 3 ∈ S ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∉ S → SplitSexticDDMM → SerreTateAt p →
      ∀ (t : ℚ) (ht : t ∉ contactSet), ¬ Odd (padicValRat p (primitiveBranch (picardParameter t))) →
      ∀ (B : GroupScheme ℚ), IsAbelianScheme B → ∀ n : ℕ, LocalPowerMaps p M ψ t ht B n →
        GoodReductionAt p B := by
  obtain ⟨S,primes,h₂,h₃,reduce⟩ := good_reduction_of_fibre M ψ
  refine ⟨S,primes,h₂,h₃,?_⟩
  intro p prime away criterion st t ht even B hB n maps
  have no₂ : p ≠ 2 := fun h => away (h ▸ h₂)
  have no₃ : p ≠ 3 := fun h => away (h ▸ h₃)
  have gt : 3 < p := by have := prime.out.two_le; omega
  obtain ⟨q,A,m,D,hq,_⟩ := family_local_cluster_jacobian p gt t ht even
  exact reduce p away criterion st t ht B hB n maps hq D

end
end ZOverQ.Qualitative.CommonWittReduction

#print axioms ZOverQ.Qualitative.CommonWittReduction.good_reduction_of_fibre
#print axioms ZOverQ.Qualitative.CommonWittReduction.good_reduction_of_clusters
#print axioms ZOverQ.Qualitative.CommonWittReduction.good_reduction_outside
