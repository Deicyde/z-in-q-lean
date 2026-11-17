import Cache
import Lower
namespace CircuitTransport
open ZeroInput.Sparse
open ProjectionDescent (Rows)

private theorem nonneg (a : Rat) : 0≤a*a := by
  by_cases h : 0≤a
  · exact Rat.mul_nonneg h h
  · have neg : 0≤ -a := by grind
    have positive := Rat.mul_nonneg neg neg;grind

private theorem sq_test (a X s : Rat) (hs : 0≤s) :
    a*a+(X*X)*s=0 ↔ a=0 ∧ (X=0 ∨ s=0) := by
  have ha := nonneg a;have hb := Rat.mul_nonneg (nonneg X) hs
  constructor
  · intro eq
    have za : a*a=0 := by grind
    have zb : X*(X*s)=0 := by grobner
    refine ⟨(Rat.mul_eq_zero.mp za).elim id id,?_⟩
    rcases Rat.mul_eq_zero.mp zb with h|h
    · exact Or.inl h
    · exact Rat.mul_eq_zero.mp h
  · rintro ⟨ha,h|h⟩ <;> grobner

private theorem simple_test (a s : Rat) (hs : 0≤s) : a*a+s=0 ↔ a=0 ∧ s=0 := by
  have th := sq_test a 1 s hs
  simpa [Rat.one_mul] using th

def rowWords (b : Book) (env : Coords) (rows : Rows) : List Word :=
  rows.map fun r => (clearRow b env r.2).num

def squares (b : Book) (start : Word) : List Word→Word
  | [] => start
  | w::ws => squares b (plus b start (times b w w)) ws

def numerical (b : Book) (x : Assignment) : List Word→Rat
  | [] => 0
  | w::ws => w.value b x*w.value b x+numerical b x ws

private theorem square_value (b : Book) (x : Assignment) (start : Word) (ws : List Word) :
    (squares b start ws).value b x=start.value b x+numerical b x ws := by
  induction ws generalizing start with
  | nil => simp [squares,numerical,Rat.add_zero]
  | cons w ws ih =>
    change (squares b (plus b start (times b w w)) ws).value b x=_
    rw [ih,plus_value,times_value];simp only [numerical];grobner

private theorem numerical_pos (b : Book) (x : Assignment) (ws : List Word) : 0≤numerical b x ws := by
  induction ws with | nil => exact Rat.le_refl | cons w ws ih => exact Rat.add_nonneg (nonneg _) ih

private theorem prior_pos (z : Assignment) (rows : Rows) : 0≤RowSquares.sumSquares z rows := by
  induction rows with | nil => exact Rat.le_refl | cons w ws ih => exact Rat.add_nonneg (nonneg _) ih

private theorem cell_zero {b x c v} (h : Represents b x c v) : c.num.value b x=0 ↔ v=0 := by
  have ne : (c.den:Rat)≠0 := fun eq => by have z := Rat.natCast_eq_zero_iff.mp eq;have p := h.1;omega
  rw [h.2];exact ⟨fun z => (Rat.mul_eq_zero.mp z).resolve_left ne, fun z => by rw [z,Rat.mul_zero]⟩

private theorem weighted_zero {b x env z} (h : Along b x env z) (rows : Rows) :
    numerical b x (rowWords b env rows)=0 ↔ RowSquares.sumSquares z rows=0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change _*_+numerical b x (rowWords b env rs)=0 ↔ _*_+RowSquares.sumSquares z rs=0
    rw [simple_test _ _ (numerical_pos _ _ _),simple_test _ _ (prior_pos _ _),cell_zero (clear_row_value h _),ih]

structure Outputs where
  ordinary : Word
  marked : Word

/-- Keep the computed pivot array as an explicit value at the evaluator boundary. -/
@[noinline] def fromTable (b : Book) (base : Coords) (stored : Array (Option Cell))
    (top : Nat×ProjectionDescent.Polynomial) (rest : Rows) : Outputs :=
  let env := select base stored
  let a := (clearRow b env top.2).num
  let s := squares b (integer b 0) (rowWords b env rest)
  let input := varWord b 1
  let a2 := times b a a
  ⟨plus b a2 s,plus b a2 (times b (times b input input) s)⟩

def outputs (b : Book) (ps : List Triangular.Pivot) (top : Nat×ProjectionDescent.Polynomial)
    (rest : Rows) (code : Nat→Nat) : Outputs :=
  let base := initial b code
  fromTable b base (cells b ps base) top rest

theorem outputs_zero (b : Book) (ps : List Triangular.Pivot) (top : Nat×ProjectionDescent.Polynomial)
    (rest : Rows) (code : Nat→Nat) (valid : Triangular.valid ps=true) (y : Fin 153→Rat) :
    ((outputs b ps top rest code).ordinary.value b (finiteLift y)=0 ↔ Triangular.ordinary ps (top::rest) code y=0) ∧
    ((outputs b ps top rest code).marked.value b (finiteLift y)=0 ↔ Triangular.marked ps top rest code y=0) := by
  let x := finiteLift y
  let z := Triangular.recov ps (Triangular.seed code y)
  let env := memo b ps (initial b code)
  let a := (clearRow b env top.2).num
  let s := squares b (integer b 0) (rowWords b env rest)
  have h : Along b x env z := by
    dsimp only [env]; rw [memo_eq]; exact restore_value (initial_value b code y) ps valid
  have ss : s.value b x=numerical b x (rowWords b env rest) := by
    change (squares b (integer b 0) _).value b x=_
    rw [square_value,integer_value,Rat.intCast_zero,Rat.zero_add]
  have ap : a.value b x=0 ↔ value z top.2=0 := cell_zero (clear_row_value h _)
  have ord := weighted_zero h rest
  constructor
  · change (plus b (times b a a) s).value b x=0 ↔ value z top.2*value z top.2+RowSquares.sumSquares z rest=0
    rw [plus_value,times_value,ss,simple_test _ _ (numerical_pos _ _ _),simple_test _ _ (prior_pos _ _),ap,ord]
  · change (plus b (times b a a) (times b (times b (varWord b 1) (varWord b 1)) s)).value b x=0 ↔
      (value z top.2)^2+(x 1)^2*RowSquares.sumSquares z rest=0
    rw [plus_value,times_value,times_value,times_value,variable_value,ss]
    have right : (value z top.2)^2+(x 1)^2*RowSquares.sumSquares z rest=
      value z top.2*value z top.2+(x 1*x 1)*RowSquares.sumSquares z rest := by grobner
    rw [right,sq_test _ _ _ (numerical_pos _ _ _),sq_test _ _ _ (prior_pos _ _),ap,ord]

end CircuitTransport
