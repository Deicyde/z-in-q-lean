import WitnessCoordinates
import Mathlib.NumberTheory.NumberField.Norm

/-! The trace pairing for a square root in a finite Galois extension. -/
namespace Sun28.FiveDescent.ResidueField
open NumberField IntermediateField Module
noncomputable section

theorem lattice_dvd {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (rank : Module.finrank ℚ K=n) (b : Fin n → 𝓞 K) :
    NumberField.discr K ∣ Algebra.discr ℤ b := by
  let e:=Module.finBasisOfFinrankEq ℤ (𝓞 K) ((RingOfIntegers.rank K).trans rank)
  have h:=Algebra.discr_of_matrix_vecMul (A:=ℤ) (e : Fin n→𝓞 K) (e.toMatrix b)
  rw [Module.Basis.toMatrix_map_vecMul,NumberField.discr_eq_discr K e] at h
  exact ⟨_,h.trans (mul_comm _ _)⟩

theorem trace_vanishing {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    {a : ℤ} {u : K} (hu : u^2=(a:K)) (irr : u∉Set.range (algebraMap ℚ K)) :
    Algebra.trace ℚ K u=0 := by
  obtain ⟨σ,hσ⟩ : ∃ σ : K≃ₐ[ℚ] K,σ u≠u := by
    by_contra! h
    exact irr ((IsGalois.mem_range_algebraMap_iff_fixed u).mpr h)
  have neg : σ u= -u :=
    (sq_eq_sq_iff_eq_or_eq_neg.mp (show (σ u)^2=u^2 by rw [←map_pow,hu,map_intCast])).resolve_left hσ
  have tr:=Algebra.trace_eq_of_algEquiv σ u
  rw [neg,map_neg] at tr
  linarith

theorem quadratic_dvd {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (rank : Module.finrank ℚ K=2) {d : ℤ} {u : K} (hu : u^2=(d:K))
    (irr : u∉Set.range (algebraMap ℚ K)) : NumberField.discr K ∣ 4*d := by
  let x : 𝓞 K:=⟨u,integral_root hu⟩
  have xx : x*x=(d:𝓞 K) := Subtype.ext (show u*u=(d:K) by simpa only [←pow_two] using hu)
  have tr : Algebra.trace ℤ (𝓞 K) x=0 := by
    apply Int.cast_injective (α:=ℚ)
    rw [Algebra.coe_trace_int,Int.cast_zero]
    exact trace_vanishing hu irr
  have tr1 : Algebra.trace ℤ (𝓞 K) 1=2 := by
    rw [←map_one (algebraMap ℤ (𝓞 K))]
    rw [Algebra.trace_algebraMap,RingOfIntegers.rank,rank];rfl
  have trd : Algebra.trace ℤ (𝓞 K) (d:𝓞 K)=2*d := by
    change Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d)=_
    rw [Algebra.trace_algebraMap,RingOfIntegers.rank,rank];rfl
  have D:=lattice_dvd rank ![1,x]
  simpa [Algebra.discr_def,Matrix.det_fin_two,Algebra.traceMatrix_apply,Algebra.traceForm_apply,
    xx,tr,tr1,trd,show (2:ℤ)*(2*d)=4*d by ring] using D

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.lattice_dvd
#print axioms Sun28.FiveDescent.ResidueField.trace_vanishing
#print axioms Sun28.FiveDescent.ResidueField.quadratic_dvd
