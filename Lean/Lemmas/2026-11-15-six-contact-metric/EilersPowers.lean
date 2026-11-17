import EilersCharacteristics
import OriginalThomae

/-! Removal of the root choices and labelling from the printed first Thomae formula. -/
namespace ZInQBlueprint.SixMetric
open OriginalTheta ThetaPeriod ThetaQuotient BranchFormula ZInQ.LeafPush2
noncomputable section

/-- Eilers (2.16), larger branch index minus smaller, for the finite pair and triple. -/
def nabla (v : Fin 5 → ℂ) (i : Fin 10) : ℂ :=
  let s := row i
  (v s.q - v s.p) * ((v s.b - v s.a)*(v s.c - v s.a)*(v s.c - v s.b))

theorem nabla_sq (v : Fin 5 → ℂ) (i : Fin 10) :
    nabla v i^2=branchValue v (pairs i) := by
  rw [branch_row]; unfold nabla; ring

/-- The square of the period prefactor in Eilers (2.17), at g=2. -/
def prefactor (detA : ℂ) := detA / (2^2 * (Real.pi:ℂ)^2)

def scaleOf (detA : ℂ) (hn : detA ≠ 0) : ℂˣ :=
  Units.mk0 ((prefactor detA)^4) (pow_ne_zero _ (div_ne_zero hn (by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp))))

/-- Each fourth root and each sign may be chosen separately on each row. -/
def FirstThomae (Ω : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 5 → ℂ) (detA : ℂ) : Prop :=
  ∀ i, ∃ ε a q : ℂ, ε^8=1 ∧ a^2=prefactor detA ∧ q^4=nabla v i ∧
    thetaConst Ω (pairChar i)=ε*a*q

theorem eighth_of_first {Ω : Matrix (Fin 2) (Fin 2) ℂ} {v : Fin 5 → ℂ} {detA : ℂ}
    (hn : detA≠0) (h : FirstThomae Ω v detA) (j : Fin 10) :
    (thetaConst Ω (characteristic (evenIndices j)))^8 =
      (scaleOf detA hn : ℂ)*branchValue v (eilersLabel j) := by
  let i := evenPosition.symm j
  have hj : evenPosition i=j := evenPosition.apply_symm_apply j
  obtain ⟨ε,a,q,he,ha,hq,ht⟩ := h i
  rw [pairChar_eq,hj] at ht
  rw [ht,mul_pow,mul_pow,he,one_mul,show a^8=(a^2)^4 by ring,
    show q^8=(q^4)^2 by ring,ha,hq,nabla_sq]
  rfl

/-- Paper sextic, printed source expression, embedding, and original PR114 coordinates. -/
theorem representative_of_first {u δ : ℚ} (hu : u∉ZInQ.contactSet) (hd : δ≠0)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (r : Fin 6 → ℂ) (hr : Function.Injective r)
    (hz : ∀ i, Polynomial.aeval (r i) (SexticThetaHeight.sextic u δ)=0)
    {detA : ℂ} (hn : detA≠0) (h : FirstThomae Ω (finiteBranches r) detA) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ),
      c≠0 ∧ (∀ m, emb (z m)=c*thetaConst Ω m) ∧ z pivot=1 :=
  marked_original_representative hu hd Ω hΩ r hr hz eilersLabel (scaleOf detA hn) (eighth_of_first hn h)

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.nabla_sq
#print axioms ZInQBlueprint.SixMetric.eighth_of_first
#print axioms ZInQBlueprint.SixMetric.representative_of_first
