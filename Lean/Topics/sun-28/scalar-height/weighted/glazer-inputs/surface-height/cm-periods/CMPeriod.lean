import RingClassBounds
import EtaProduct
import CMRingField
import Mathlib.NumberTheory.NumberField.ClassNumber
namespace ZInQBlueprint.CMPeriods
noncomputable section
/-- A reduced positive binary form and its root in the upper half-plane. -/
structure ReducedPeriod (d : ℕ) (z : ℂ) where
  a : ℕ
  b : ℤ
  c : ℕ
  positive : 0 < a
  reducedB : b.natAbs ≤ a
  reducedC : a ≤ c
  upper : 0 < z.im
  root : (a:ℂ)*z^2+(b:ℂ)*z+c=0
  discr : (d:ℤ) = 4*(a:ℤ)*c-b^2

theorem period_range {d : ℕ} {z : ℂ} (P : ReducedPeriod d z)
    (bound : d ≤ 71424^2) : 1/2 ≤ z.im ∧ z.im ≤ 35712 := by
  let a : ℝ := P.a
  let b : ℝ := P.b
  let c : ℝ := P.c
  have ap : (1:ℝ)≤a := by dsimp [a]; exact_mod_cast (show 1≤P.a from P.positive)
  have ac : a≤c := by dsimp [a,c]; exact_mod_cast P.reducedC
  have bh : |b|≤a := by simpa only [b,a,Nat.cast_natAbs,Int.cast_abs] using (show (P.b.natAbs:ℝ)≤P.a by exact_mod_cast P.reducedB)
  have bb : b^2 ≤ a^2 := (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr bh |> fun h => by simpa using h
  have D : (d:ℝ) = 4*a*c-b^2 := by dsimp [a,b,c]; exact_mod_cast P.discr
  have top : (d:ℝ)≤71424^2 := by exact_mod_cast bound
  have re := congrArg Complex.re P.root
  have im := congrArg Complex.im P.root
  simp only [pow_two,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
    Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,Complex.intCast_im,
    Complex.zero_re,Complex.zero_im,zero_mul,add_zero,sub_zero] at re im
  change a*(z.re*z.re-z.im*z.im)+b*z.re+c=0 at re
  have im' : (2*a*z.re+b)*z.im=0 := by
    dsimp [a,b]
    linear_combination im
  have bx := (mul_eq_zero.mp im').resolve_right P.upper.ne'
  have disc : (2*a*z.im)^2=(d:ℝ) := by
    linear_combination -4*a*re + (2*a*z.re+b)*bx - D
  have low : a^2 ≤ (2*a*z.im)^2 := by
    rw [disc,D]
    nlinarith only [bb,mul_nonneg (show 0≤a by linarith) (sub_nonneg.mpr ac),sq_nonneg a]
  have ar : 0<a := by linarith
  have pos := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ar.le) P.upper.le
  have l := (sq_le_sq₀ ar.le pos).mp low
  have u := (sq_le_sq₀ pos (by norm_num : (0:ℝ)≤71424)).mp (disc.trans_le top)
  constructor
  · by_contra! hz
    nlinarith only [l,mul_pos ar (sub_pos.mpr hz)]
  · nlinarith only [u, mul_nonneg (sub_nonneg.mpr ap) P.upper.le]

/-- Watkins, Table 4. This is a statement about Mathlib's class number and
field discriminant, specialized only by the range of class numbers needed. -/
def SmallClassDiscriminants : Prop := ∀ (K : IntermediateField ℚ ℂ) [NumberField K],
  Module.finrank ℚ K = 2 → NumberField.discr K < 0 → NumberField.classNumber K ≤ 16 →
    (NumberField.discr K).natAbs ≤ 34483

/-- The classical input for a CM point of the maximal-order curve. The
field L is its residue field, and K is its imaginary quadratic CM field. -/
structure OrderFibre where
  K : IntermediateField ℚ ℂ
  fieldK : NumberField K
  L : IntermediateField ℚ ℂ
  finiteL : FiniteDimensional ℚ L
  X : Type
  finiteX : Fintype X
  lift : (L →ₐ[ℚ] ℂ) → X
  separates : Function.Injective lift
  cover : Fin 16 → X
  transitive : Function.Surjective cover
  conductor : ℕ
  conductor_pos : 0 < conductor
  orderClassNumber : ℕ
  quadratic : Module.finrank ℚ K = 2
  imaginary : letI := fieldK; NumberField.discr K < 0
  reciprocity : Module.finrank ℚ ↥(K ⊔ L) = 2*orderClassNumber
  extensionOfIdeals : letI := fieldK; NumberField.classNumber K ∣ orderClassNumber
  unitsIndex : ℕ
  units_le : unitsIndex ≤ 3
  eulerTerm : ℕ → ℕ
  symbol_le : ∀ p ∈ conductor.primeFactors, p-1 ≤ eulerTerm p
  classFormula : letI := fieldK
                 unitsIndex*orderClassNumber = NumberField.classNumber K *
                   ∏ p ∈ conductor.primeFactors, p^(conductor.factorization p-1)*eulerTerm p
  class_pos : 0 < orderClassNumber
attribute [instance] OrderFibre.fieldK OrderFibre.finiteL OrderFibre.finiteX

def orderDiscriminant (F : OrderFibre) : ℕ := F.conductor^2*(NumberField.discr F.K).natAbs

theorem order_bound (table : SmallClassDiscriminants) (F : OrderFibre) :
    orderDiscriminant F ≤ 71424^2 := by
  have h := ring_class_degree_le F.K F.L F.quadratic F.reciprocity (residue_degree_le F.lift F.separates F.cover F.transitive)
  have hk := (Nat.le_of_dvd F.class_pos F.extensionOfIdeals).trans h
  have d := table F.K F.quadratic F.imaginary hk
  have phi := totient_le_class_index F.conductor_pos (NumberField.classNumber_pos F.K) F.eulerTerm F.symbol_le F.classFormula
  have f := conductor_le F.conductor_pos (phi.trans ((Nat.mul_le_mul F.units_le h) : F.unitsIndex*F.orderClassNumber≤48))
  unfold orderDiscriminant
  exact (Nat.mul_le_mul (Nat.pow_le_pow_left f _) d).trans (by decide)

/-- Saia's product and the elliptic discriminant formula give the sum of
the period heights of the two factors, averaged over a good-reduction field. -/
structure PeriodPresentation (height : ℝ) where
  fibre : OrderFibre
  field : IntermediateField ℚ ℂ
  finite : FiniteDimensional ℚ field
  periods : Fin 2 → (field →ₐ[ℚ] ℂ) → ℂ
  forms : ∀ i σ, ReducedPeriod (orderDiscriminant fibre) (periods i σ)
  faltings : letI := finite
             height = (∑ σ, ∑ i, periodHeight (periods i σ))/(Module.finrank ℚ field:ℝ)

theorem surface_le (table : SmallClassDiscriminants) {h : ℝ} (A : PeriodPresentation h) : h ≤ 71430 := by
  let := A.finite
  have bd := order_bound table A.fibre
  have each (σ) (i) : periodHeight (A.periods i σ) ≤ 35715 := by
    have yz := period_range (A.forms i σ) bd
    exact (periodHeight_le yz.1).trans (by linarith only [yz.2])
  rw [A.faltings]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Module.finrank_pos (R:=ℚ) (M:=A.field)))).2
  calc
    _ ≤ ∑ _σ : A.field →ₐ[ℚ] ℂ, ∑ _i : Fin 2, (35715:ℝ) :=
      Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun i _ => each σ i))
    _ = _ := by simp [AlgHom.card]; ring
end
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.period_range
#print axioms ZInQBlueprint.CMPeriods.order_bound
#print axioms ZInQBlueprint.CMPeriods.surface_le
