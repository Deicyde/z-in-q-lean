import OriginalThetaSeries
import ThomaeEighthPowers
import ThomaeBranchPoints
import ThetaParity

namespace ZInQBlueprint.OriginalTheta
open ThetaPeriod ThetaQuotient ZInQ.LeafPush2 SexticInvariants
noncomputable section

def pivot : Char2 := characteristic (evenIndices 0)

/-- Ratios on the draft normalization are algebraic relative to its
zero characteristic once the common-scale Thomae identities hold. -/
theorem original_ratios (Z : SiegelPeriod) (T : EighthPowerData (thetaNull Z)) (m : Char2) :
    IsAlgebraic ℚ (thetaConst (omega Z) m / thetaConst (omega Z) pivot) := by
  obtain ⟨j,rfl⟩ := characteristicEquiv.surjective m
  change IsAlgebraic ℚ (thetaConst (omega Z) (characteristic j) / thetaConst (omega Z) (characteristic (evenIndices 0)))
  rw [thetaConst_eq,thetaConst_eq]
  exact eighth_ratios_algebraic T j

/-- All original coordinates have one number-field representative and the
single nonzero complex scale in R22_Pazuki's hypothesis. -/
theorem original_representative (Z : SiegelPeriod) (T : EighthPowerData (thetaNull Z)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ),
      c≠0 ∧ (∀ m, emb (z m)=c*thetaConst (omega Z) m) ∧ z pivot=1 := by
  let a := chart (thetaNull Z)
  let L := fieldOf a
  let inst := numberField a (eighth_ratios_algebraic T)
  let z : Char2 → L := fun m => coordinates a (characteristicEquiv.symm m)
  let c := (thetaNull Z (evenIndices 0))⁻¹
  have hp := chart_pivot (eighth_even_nonzero T)
  refine ⟨L,inferInstance,inferInstance,(fieldOf a).subtype,z,c,inv_ne_zero hp,?_,?_⟩
  · intro m
    obtain ⟨j,rfl⟩ := characteristicEquiv.surjective m
    change ((coordinates a (characteristicEquiv.symm (characteristicEquiv j)):fieldOf a):ℂ) = c*thetaConst (omega Z) (characteristic j)
    rw [characteristicEquiv.symm_apply_apply,coordinates_embed,thetaConst_eq]
    dsimp [a,chart,c]
    ring
  · apply Subtype.ext
    change a (characteristicEquiv.symm (characteristicEquiv (evenIndices 0)))=1
    rw [characteristicEquiv.symm_apply_apply]
    exact div_self hp

/-- For the actual sextic, only the labelled first Thomae identities at its
six specified roots are used; odd vanishing and branch algebraicity are proved. -/
theorem marked_original_representative {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hδ : δ≠0)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (r : Fin 6 → ℂ) (distinct : Function.Injective r)
    (root : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    (label : Fin 10 ≃ Partition) (scale : ℂˣ)
    (id : ∀ i, (thetaConst Ω (characteristic (evenIndices i)))^8=
      (scale:ℂ)*branchValue (finiteBranches r) (label i)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ),
      c≠0 ∧ (∀ m, emb (z m)=c*thetaConst Ω m) ∧ z pivot=1 := by
  let Z := periodOf Ω hΩ
  have eq : omega Z=Ω := omega_periodOf Ω hΩ
  have T := of_sextic_thomae (z:=thetaNull Z) hu hδ r distinct root label scale
    (fun i => by simpa only [←eq,thetaConst_eq] using id i) (thetaNull_odd Z)
  simpa only [eq] using original_representative Z T

end
end ZInQBlueprint.OriginalTheta
#print axioms ZInQBlueprint.OriginalTheta.original_ratios
#print axioms ZInQBlueprint.OriginalTheta.original_representative
#print axioms ZInQBlueprint.OriginalTheta.marked_original_representative
