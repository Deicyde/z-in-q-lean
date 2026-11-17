import SparseMetric
import ArchimedeanDescent

/-! Exact difference between the Euclidean and sup metrics, expressed through eighth powers. -/
namespace ZInQBlueprint.SixMetric
open Function ThetaQuotient Height Height.AdmissibleAbsValues NumberField
noncomputable section

abbrev fourthRoot (x : ℝ) := Real.sqrt (Real.sqrt x)
abbrev eighthRoot (x : ℝ) := Real.sqrt (Real.sqrt (Real.sqrt x))

/-- The local quotient of (sum |wᵢ|^(1/4))^(1/2) and max |wᵢ|^(1/8). -/
def rootDistortion (a : Fin 10 → ℝ) : ℝ :=
  Real.sqrt (∑ i, fourthRoot (a i)) / (⨆ i, eighthRoot (a i))

private theorem eighth_power {s : ℝ} (hs : 0 ≤ s) :
    fourthRoot (s^8)=s^2 ∧ eighthRoot (s^8)=s := by
  have h : s^8 = ((s^2)^2)^2 := by ring
  rw [h]
  simp [fourthRoot,eighthRoot,Real.sqrt_sq hs,Real.sqrt_sq (sq_nonneg s),
    Real.sqrt_sq (sq_nonneg (s^2))]

theorem correction_of_coordinates {K : Type*} [Field K] [NumberField K] (x : Fin 10 → K) (hx : x≠0) :
    euclideanHeight x=normalizedHeight x+
      (∑ σ : K →+* ℂ, Real.log (rootDistortion (fun i => ‖σ ((x i)^8)‖))) /
        (Module.finrank ℚ K : ℝ) := by
  classical
  let A (v : AbsoluteValue K ℝ) := Real.sqrt (∑ i, v (x i)^2)
  let M (v : AbsoluteValue K ℝ) := ⨆ i, v (x i)
  have hM (v : AbsoluteValue K ℝ) : 0<M v := by
    obtain ⟨i,hi⟩ := ne_iff.mp hx
    exact (v.pos_iff.mpr hi).trans_le (Finite.le_ciSup (fun j => v (x j)) i)
  have hA (v : AbsoluteValue K ℝ) : 0<A v := by
    obtain ⟨i,hi⟩ := ne_iff.mp hx
    apply Real.sqrt_pos.mpr
    exact (sq_pos_of_pos (v.pos_iff.mpr hi)).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (v (x j))) (Finset.mem_univ i))
  let C (v : AbsoluteValue K ℝ) := A v / M v
  have hC (v : AbsoluteValue K ℝ) : 0<C v := div_pos (hA v) (hM v)
  have hAM : (archAbsVal.map A).prod=(archAbsVal.map C).prod*(archAbsVal.map M).prod := by
    rw [←Multiset.prod_map_mul]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro v _
    exact (div_mul_cancel₀ (A v) (hM v).ne').symm
  have hp : (archAbsVal.map C).prod=∏ φ : K →+* ℂ, C (InfinitePlace.mk φ).val := by
    rw [NumberField.prod_archAbsVal_eq]
    exact (HeightDescent.prod_embeddings (fun w : InfinitePlace K => C w.val)).symm
  have cLog : Real.log (archAbsVal.map C).prod =
      ∑ φ : K →+* ℂ, Real.log (rootDistortion (fun i => ‖φ ((x i)^8)‖)) := by
    rw [hp,Real.log_prod (fun φ _ => (hC (InfinitePlace.mk φ).val).ne')]
    apply Finset.sum_congr rfl
    intro φ _
    let v := (InfinitePlace.mk φ).val
    change Real.log (A v/M v)=_
    congr 1
    have hn (i : Fin 10) : ‖φ ((x i)^8)‖=(v (x i))^8 := by rw [map_pow,norm_pow]; rfl
    have h₄ (i : Fin 10) := (eighth_power (v.nonneg (x i))).1
    have h₈ (i : Fin 10) := (eighth_power (v.nonneg (x i))).2
    simp only [rootDistortion,hn,h₄,h₈,A,M]
  change (if x=0 then 0 else Real.log ((archAbsVal.map A).prod *
      ∏ᶠ w : nonarchAbsVal, ⨆ i, w.val (x i)) / _) = _
  rw [ite_eq_right hx,hAM,mul_assoc,←Height.mulHeight_eq hx,Real.log_mul
    (by rw [hp]; exact (Finset.prod_pos fun φ _ => hC (InfinitePlace.mk φ).val).ne')
    (Height.mulHeight_pos x).ne',cLog,normalizedHeight,logHeight_eq_log_mulHeight]
  ring

/-- The normalized archimedean correction is intrinsic to the number field of the weights. -/
def branchCorrection {K : Type*} [Field K] [NumberField K] (w : Fin 10 → K) :=
    (∑ φ : K →+* ℂ, Real.log (rootDistortion (fun i => ‖φ (w i)‖))) /
      (Module.finrank ℚ K:ℝ)

theorem correction_map {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (e : K →+* L) (w : Fin 10 → K) : branchCorrection (fun i => e (w i))=branchCorrection w := by
  classical
  let : Algebra K L := e.toAlgebra
  let a (φ : K →+* ℂ) := Real.log (rootDistortion (fun i => ‖φ (w i)‖))
  have h : (∑ σ : L →+* ℂ, a (σ.comp e))=(Module.finrank K L:ℝ)*∑ φ, a φ := by
    rw [←Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp e),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro φ _
    calc
      (∑ σ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp e=φ), a (σ.comp e)) =
        ∑ _σ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp e=φ), a φ :=
        Finset.sum_congr rfl fun _ hσ => congrArg a (Finset.mem_filter.mp hσ).2
      _ = _ := by
        have card : (Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp e=φ)).card = Module.finrank K L :=
          HeightDescent.embedding_fiber_card (L:=L) φ
        rw [Finset.sum_const,card,nsmul_eq_mul]
  have : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  have hd : (Module.finrank K L:ℝ)≠0 := by exact_mod_cast (Module.finrank_pos (R:=K) (M:=L)).ne'
  unfold branchCorrection
  change (∑ σ : L →+* ℂ, a (σ.comp e))/_=_
  rw [h,←Module.finrank_mul_finrank ℚ K L,Nat.cast_mul]
  dsimp [a]
  field_simp

end
end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.correction_of_coordinates
#print axioms ZInQBlueprint.SixMetric.correction_map
