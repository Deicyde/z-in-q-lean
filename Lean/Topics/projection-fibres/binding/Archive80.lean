import Flat80Arithmetic

namespace ProjectionFibres.Binding
open CircuitTransport StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.Actual
set_option maxRecDepth 16384
private theorem at_address (y : Fin 80→Rat) (i : Nat) (a : i<9918) (b : phase i≤1) :
    V y (address i)=wire (filled y) i := Eq.symm (fromParent y i a b)
private theorem map_values (s : List Nat) (p : Nat→Nat) (f g : Nat→Rat)
    (h : ∀ i∈s,f (p i)=g i) : (s.map p).map f=s.map g := by
  rw [List.map_map];exact List.map_congr_left h
private theorem at_retained (y : Fin 80→Rat) (i : Nat) (hi : i∈retained) :
    V y (address i)=wire (filled y) i := by
  have lim := of_decide_eq_true (List.all_eq_true.mp row_phases i hi)
  exact at_address y i lim.1 lim.2
theorem retained_values (y : Fin 80→Rat) :
    (retained.map address).map (V y)=retained.map (wire (filled y)) :=
  map_values retained address (V y) (wire (filled y)) (at_retained y)
private theorem curve_on_fill (b₀ : Base) (a b : Rat) :
    wire (fill b₀ a b 0 0 0 0) 513=curve a b (data b₀).z (data b₀).w :=
  curve_row (fill b₀ a b 0 0 0 0)
theorem curve_value (y : Fin 80→Rat) :
    V y 9135=curve (first y) (second y) (F y).z (F y).w := by
  have pos : address 513=9135 := by decide +kernel
  have pair:=(fromParent y 513 (by decide) (by decide +kernel)).symm
  rw [pos] at pair
  exact pair.trans (curve_on_fill (B y) (first y) (second y))
theorem mapped_rows (y : Fin 80→Rat) :
    V y 9135 :: V y 9758 :: (retained.map address).map (V y)=reducedRows (B y) (y 78) (y 79) := by
  change _=curve (first y) (second y) (F y).z (F y).w ::
      homogeneousPole (F y).t (F y).s (F y).j ((F y).N (norm y)) (F y).D ::
      retained.map (wire (filled y))
  exact List.cons_eq_cons.mpr ⟨curve_value y,List.cons_eq_cons.mpr ⟨hom_value y,retained_values y⟩⟩

theorem ordinary_pointwise (y : Fin 80→Rat) : V y 9813=output80 false y :=
  (archive_sum y).trans (congrArg squares (mapped_rows y))

/-- Universal evaluation equality for both outputs of the archived integer tape. -/
theorem physical_pointwise (marked : Bool) (y : Fin 80→Rat) :
    V y (if marked then 9814 else 9813)=output80 marked y := by
  cases marked with
  | false=>exact ordinary_pointwise y
  | true=>change V y 9814=y 0*output80 false y;rw [v9814,v0,ordinary_pointwise]

theorem physical_projection (marked : Bool) (T : Rat) :
    (∃ x : Fin 84→Rat, cell x 1=T ∧ output marked x=0) ↔
    ∃ y : Fin 80→Rat, y 0=T ∧ V y (if marked then 9814 else 9813)=0 := by
  simp only [physical_pointwise]
  exact projection_iff marked T

#print axioms ProjectionFibres.Binding.map_value
#print axioms ProjectionFibres.Binding.copyParent
#print axioms ProjectionFibres.Binding.guard_value
#print axioms ProjectionFibres.Binding.hom_value
#print axioms ProjectionFibres.Binding.mapped_rows
#print axioms ProjectionFibres.Binding.ordinary_pointwise
#print axioms ProjectionFibres.Binding.physical_pointwise
#print axioms ProjectionFibres.Binding.physical_projection

end ProjectionFibres.Binding
