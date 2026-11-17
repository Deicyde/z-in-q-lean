import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! A single finite splitting field captures every value of a finite algebra in
every overfield. An extra polynomial may be included in the same extension. -/
open Polynomial
namespace ZInQBlueprint.TorsionHeight
noncomputable section
universe u v w
variable (F : Type u) [Field F] (R : Type v) [CommRing R] [Algebra F R] [Module.Finite F R]

private abbrev basis := Module.finBasis F R

def kernelPolynomial : F[X] := ∏ i, minpoly F (basis F R i)

theorem kernelPolynomial_monic : (kernelPolynomial F R).Monic := by
  classical
  exact monic_prod_of_monic _ _ (fun i _ => minpoly.monic (Algebra.IsIntegral.isIntegral (basis F R i)))

/-- Splitting the polynomial of the section algebra places every value on every
geometric point in the field itself. No normality of the overfield is assumed. -/
theorem factors_of_splits {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (i : K →ₐ[F] L) (s : ((kernelPolynomial F R).map (algebraMap F K)).Splits)
    (v : R →ₐ[F] L) : ∃ w : R →ₐ[F] K, i.comp w = v := by
  classical
  let b := basis F R
  have vals (j : Fin (Module.finrank F R)) : v (b j) ∈ i.range := by
    let p := minpoly F (b j)
    have hp : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
    have divides : p ∣ kernelPolynomial F R := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have sp := s.of_dvd ((kernelPolynomial_monic F R).map _).ne_zero (map_dvd (mapRingHom (algebraMap F K)) divides)
    have root : ((p.map (algebraMap F K)).map i.toRingHom).IsRoot (v (b j)) := by
      rw [map_map]
      have hi : i.toRingHom.comp (algebraMap F K) = algebraMap F L := RingHom.ext i.commutes
      rw [hi]
      change (p.map (algebraMap F L)).eval (v (b j)) = 0
      rw [←eval₂_eq_eval_map,←aeval_def,aeval_algHom_apply,minpoly.aeval,_root_.map_zero]
    exact sp.mem_range_of_isRoot (hp.map _).ne_zero root
  have allvals (x : R) : v x ∈ i.range := by
    rw [←b.sum_repr x, map_sum]
    apply Subalgebra.sum_mem
    intro j _
    rw [map_smul]
    exact (i.range).smul_mem (vals j) _
  let w := v.codRestrict i.range allvals
  let e := AlgEquiv.ofInjectiveField i
  refine ⟨e.symm.toAlgHom.comp w, ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply (w x))

/-- The auxiliary extension also splits a prescribed nonzero polynomial such as
the sextic branch polynomial of a hyperelliptic curve. -/
theorem exists_splitting_field (f : F[X]) (hf : f ≠ 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K),
      (f.map (algebraMap F K)).Splits ∧
        ∀ (L : Type w) [Field L] [Algebra F L] (i : K →ₐ[F] L) (v : R →ₐ[F] L),
          ∃ w : R →ₐ[F] K, i.comp w = v := by
  let g := f * kernelPolynomial F R
  let K := g.SplittingField
  have hg := SplittingField.splits (K := F) g
  have h0 := Polynomial.map_ne_zero (f := algebraMap F K) (mul_ne_zero hf (kernelPolynomial_monic F R).ne_zero)
  refine ⟨K,inferInstance,inferInstance,inferInstance, ?_, ?_⟩
  · exact hg.of_dvd h0 (map_dvd (mapRingHom (algebraMap F K)) (dvd_mul_right f _))
  · intro L _ _ i v
    exact factors_of_splits F R i
      (hg.of_dvd h0 (map_dvd (mapRingHom (algebraMap F K)) (dvd_mul_left _ _))) v

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.kernelPolynomial_monic
#print axioms ZInQBlueprint.TorsionHeight.factors_of_splits
#print axioms ZInQBlueprint.TorsionHeight.exists_splitting_field
