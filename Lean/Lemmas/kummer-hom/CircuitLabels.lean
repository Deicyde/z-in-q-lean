import SignedLabels
import ActualCircuit

namespace EllipticOrbit.SignedLabels
open EllipticHeight EllipticHeight.QuadraticInt
open EllipticOrbit.Field
open ProjectionFibres ProjectionFibres.Actual
open PhysicalProjection.Comparison (Q2)
open PhysicalProjection.RootOrdinate (root)
open IndependentIndices

private theorem denominator_square (a : EllipticHeight.QuadraticInt.R) :
    orderMap (Field.asOrder (sq a))=(orderMap (Field.asOrder a))^2 := by
  change orderMap (Field.asOrder a*Field.asOrder a)=_
  rw [map_mul,pow_two]

private theorem chart_fraction {h j : Q2} (rt : root h j)
    {a b : EllipticHeight.QuadraticInt.R} (frac : represents h a b) :
    Law.Rep (D:=Field.D) (chartPoint rt)
      (orderMap (Field.asOrder (sq a))) (orderMap (Field.asOrder (sq b))) := by
  have cross:=(fraction_iff h a b).mp frac.2
  have nonzero : orderMap (Field.asOrder b)≠0 := by
    intro hb
    have o:=orderMap_injective (hb.trans orderMap.map_zero.symm)
    exact frac.1 (congrArg (fun p : Field.O=>(p.re,p.im)) o)
  apply (Law.rep_some (quartic_nonsingular rt)).mpr
  rw [denominator_square,denominator_square,←cross,mul_pow]
  exact ⟨pow_ne_zero 2 nonzero,rfl⟩

private theorem rep_natAbs {n : ℤ} {a b : K} (h : Law.Rep (D:=Field.D) (n • P) a b) :
    Law.Rep (D:=Field.D) (n.natAbs • P) a b := by
  cases n with
  | ofNat k => simpa only [natCast_zsmul] using h
  | negSucc k =>
    rw [negSucc_zsmul] at h
    exact Law.rep_neg.mp h

private theorem index_zero {n : ℤ} (h : n • P=0) : n=0 := by
  cases n with
  | ofNat k =>
    have z : k • P=0 := by simpa only [natCast_zsmul] using h
    by_cases zero : k=0
    · simp [zero]
    · exact (no_positive_multiple_zero k zero z).elim
  | negSucc k =>
    have z : (k+1) • P=0 := by simpa only [negSucc_zsmul,neg_eq_zero] using h
    exact (no_positive_multiple_zero (k+1) (by omega) z).elim

theorem index_injective : Function.Injective (fun n : ℤ=>n • P) := by
  intro i j eq
  change i • P=j • P at eq
  have z : (i-j) • P=0 := by simp [sub_zsmul,eq]
  exact sub_eq_zero.mp (index_zero z)

/-- For every zero and every allowed choice of reduced physical representatives,
    the actual selection interface receives precisely the nonzero signed labels.
    Each label is unique at its prescribed signed ordinate. -/
theorem physical_labelling (group : Generated) {y : Fin 80 → Rat} (zero : Binding.V y 9813=0)
    (f : RootFractions y) :
    ∃ s : IndependentIndices.Labels, PhysicalLabelling f s ∧ ∀ i, label s i≠0 ∧
      ∀ k : ℤ, chartPoint (EllipticHeight.Labels.physical_root_charts y zero i).1=k • P ↔
        k=label s i := by
  obtain ⟨n,hn⟩:=physical_labels group y zero
  let s : IndependentIndices.Labels:=⟨n 0,n 1,n 2,n 3⟩
  have atIndex (i : Fin 4) : label s i=n i := by fin_cases i <;> rfl
  refine ⟨s,?_,?_⟩
  · intro i
    have rep:=chart_fraction (EllipticHeight.Labels.physical_root_charts y zero i).1 (f.point i)
    rw [(hn i).2] at rep
    rw [atIndex]
    exact rep_natAbs rep
  · intro i
    rw [atIndex]
    refine ⟨(hn i).1,fun k=>?_⟩
    rw [(hn i).2]
    constructor
    · intro he
      exact (index_injective he).symm
    · rintro rfl
      rfl

end EllipticOrbit.SignedLabels

#print axioms EllipticOrbit.SignedLabels.index_injective
#print axioms EllipticOrbit.SignedLabels.physical_labelling
