import Published
namespace CircuitTransport
open ZeroInput.Sparse
open Triangular.Data (ps top rest code back)
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

abbrev source (g : Bool) := Triangular.parent (ps g) (top::rest g)
abbrev context (g : Bool) := Book.make (Seeds.nodes g)

def coordinates (g : Bool) := memo (context g) (ps g) (initial (context g) code)
def reconstructed (g : Bool) (y : Fin 153→Rat) := Triangular.recov (ps g) (Triangular.seed code y)

theorem every_coordinate (g : Bool) (y : Fin 153→Rat) :
    Along (context g) (finiteLift y) (coordinates g) (reconstructed g y) := by
  unfold coordinates;rw [memo_eq];exact restore_value (initial_value _ _ _) _ (Triangular.Data.good0 g)

theorem every_row (g : Bool) (y : Fin 153→Rat) (r : ProjectionDescent.Polynomial) :
    Represents (context g) (finiteLift y) (clearRow (context g) (coordinates g) r) (value (reconstructed g y) r) :=
  clear_row_value (every_coordinate g y) r

def designated (i : Fin 153) : Rat := Triangular.Data.w (back (i.val+1))

theorem designated_zero (g : Bool) : finiteLift designated 1=0 ∧ (published g).eval true (finiteLift designated)=0 := by
  let v := Triangular.Data.w
  let x : Assignment := fun i => (v i:Rat)
  have free {i : Nat} (lo : 1≤i) (hi : i≤153) : finiteLift designated i=(v (back i):Rat) := by
    rw [Triangular.finite_at _ lo hi];change (v (back (i-1+1)):Rat)=_;rw [show i-1+1=i by omega]
  have one : finiteLift designated 1=0 := by
    rw [free (by decide) (by decide),show back 1=1 by decide]
    have zero : v 1=0 := by decide
    rw [zero];rfl
  have agree : ProjectionDescent.off (Triangular.slots (ps g)) x (Triangular.seed code designated) := by
    intro i outside;by_cases inside : Triangular.inside i=true
    · obtain ⟨lo,hi,inv⟩ := Triangular.Data.rangeTable g i inside outside
      simp [Triangular.seed,inside,free lo hi,inv,x]
    · change Triangular.seed code designated i=(Triangular.Data.w i:Rat)
      simp [Triangular.seed,Triangular.Data.w,inside]
  have ok : ∀ p∈ps g,p.ok x := by
    intro p hp
    apply (ProjectionDescent.pivot_cell p.pre p.post p.slot p.lead x).mp
    change value (fun i => (v i:Rat)) p.row=0
    have check := of_decide_eq_true (List.all_eq_true.mp (Triangular.Data.zero0 g) p hp)
    rw [←Triangular.int_value,show Triangular.intVal v p.row=0 from check];rfl
  have restore : reconstructed g designated=x :=
    (Triangular.recov_eq _ (Triangular.Data.good0 g) x _ agree).symm.trans (Triangular.fixed _ (Triangular.Data.good0 g) x ok)
  have topZero : value x top.2=0 := by
    change value (fun i => (v i:Rat)) top.2=0
    rw [←Triangular.int_value,show Triangular.intVal v top.2=0 by decide];rfl
  refine ⟨one,(pointwise g designated).2.mpr ?_⟩
  change (value (reconstructed g designated) top.2)^2+(finiteLift designated 1)^2*_=0
  rw [restore,topZero,one];grobner

private theorem parentSquares (g : Bool) (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (source g))=0) ↔
      ProjectionDescent.RowsProject 226 (source g) a := by
  constructor <;> rintro ⟨x,inp,h⟩
  · exact ⟨x,inp,(RowSquares.zero_iff_rows _ _).mp h⟩
  · exact ⟨x,inp,(RowSquares.zero_iff_rows _ _).mpr h⟩

theorem ordinary_polynomial (g : Bool) (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (source g))=0) ↔
      ∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt (published g).nodes (finiteLift y) (published g).ordinary=0 :=
  (parentSquares g a).trans (ordinary_projection g a)

theorem marked_polynomial (g : Bool) (a : Rat) :
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt (published g).nodes (finiteLift y) (published g).marked=0) ↔
      (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (source g))=0) ∨ a=0 := by
  exact (marked_projection g a).trans (or_congr (parentSquares g a).symm Iff.rfl)

end CircuitTransport
#print axioms CircuitTransport.every_row
#print axioms CircuitTransport.every_coordinate
#print axioms CircuitTransport.designated_zero
#print axioms CircuitTransport.ordinary_polynomial
#print axioms CircuitTransport.marked_polynomial
