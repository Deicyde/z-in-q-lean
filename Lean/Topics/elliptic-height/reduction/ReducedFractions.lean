import FractionArithmetic
import PrimitiveNorm

namespace EllipticHeight.Reduction
open QuadraticInt Primitive ProjectionFibres ProjectionFibres.Actual
open PhysicalProjection.Comparison (Q2)

/-- Every element of Q(√2) in its two rational coefficients has an integral
Bézout-coprime numerator and denominator in the project's representation. -/
theorem reduced_fraction (h : Q2) : ∃ a b : R, represents h a b ∧ coprime a b := by
  obtain ⟨a,b,live,fraction,bez⟩:=primitive_coefficients h
  exact ⟨a,b,⟨live,fraction⟩,bez⟩

theorem signed_chart_fraction {h j : Q2} (root : PhysicalProjection.RootOrdinate.root h j) :
    ∃ a b c : R, represents h a b ∧ coprime a b ∧ chart a b c ∧
      ∀ n, State (iterate n (sq a) (sq b)).1 (iterate n (sq a) (sq b)).2 := by
  obtain ⟨a,b,frac,pr⟩:=reduced_fraction h
  obtain ⟨c,weighted⟩:=clear_chart root frac
  exact ⟨a,b,c,frac,pr,weighted,fun n=>
    iterate_state n (start pr (dyadic_denominator weighted) (no_seven_numerator pr weighted))⟩

/-- All integral data required by the normalized duplication at one actual circuit slot. -/
def StoredChart (s : Fin 80→Rat) (i : Fin 4) (a b c : R) : Prop :=
  represents (Labels.rootH (decoded s) i) a b ∧ coprime a b ∧ chart a b c ∧
  represents (roots (decoded s) i) (sq a) (sq b) ∧
  ∀ n, State (iterate n (sq a) (sq b)).1 (iterate n (sq a) (sq b)).2

theorem stored_chart (s : Fin 80→Rat) (zero : Binding.V s 9813=0) (i : Fin 4) :
    ∃ a b c : R, StoredChart s i a b c := by
  obtain ⟨root,_,_⟩:=Labels.physical_root_charts s zero i
  obtain ⟨a,b,c,frac,pr,weighted,all⟩:=signed_chart_fraction root
  exact ⟨a,b,c,frac,pr,weighted,physical_square_representation s i frac,all⟩

/-- The circuit equation alone supplies all four primitive charts and every
raw homogeneous iterate, with one choice of representatives for all depths. -/
theorem stored_charts (s : Fin 80→Rat) (zero : Binding.V s 9813=0) :
    ∃ a b c : Fin 4→R, ∀ i, StoredChart s i (a i) (b i) (c i) := by
  let first (i : Fin 4):=stored_chart s zero i
  let second (i : Fin 4):=Classical.choose_spec (first i)
  let third (i : Fin 4):=Classical.choose_spec (second i)
  exact ⟨fun i=>Classical.choose (first i),fun i=>Classical.choose (second i),
    fun i=>Classical.choose (third i),fun i=>Classical.choose_spec (third i)⟩

theorem signed_normalized_iterate {h j : Q2} {x y u v : R}
    (root : PhysicalProjection.RootOrdinate.root h j)
    (source : represents (PhysicalProjection.Comparison.sq h) x y) (xy : coprime x y)
    (n : Nat) (uv : coprime u v)
    (cross : mul (iterate n x y).1 v=mul u (iterate n x y).2) :
    (norm (iterate n x y).1).natAbs=(norm u).natAbs := by
  obtain ⟨_,_,frac,bez⟩:=reduced_fraction h
  exact signed_iterate_norm root frac bez source xy n uv cross

theorem signed_normalized_double {h j : Q2} {x y u v : R}
    (root : PhysicalProjection.RootOrdinate.root h j)
    (source : represents (PhysicalProjection.Comparison.sq h) x y) (xy : coprime x y)
    (uv : coprime u v) (cross : mul (top x y) v=mul u (bottom x y)) :
    (norm (top x y)).natAbs=(norm u).natAbs :=
  signed_normalized_iterate root source xy 1 uv cross

#print axioms reduced_fraction
#print axioms signed_chart_fraction
#print axioms stored_chart
#print axioms stored_charts
#print axioms signed_normalized_iterate
#print axioms signed_normalized_double
end EllipticHeight.Reduction
