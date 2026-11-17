import Lower
import OriginTape

namespace IndependentIndices
open CircuitTransport

/-- Local variable numbers start at zero. A route gives the corresponding one-based
    coordinates of the ambient circuit. A missing local variable has value zero. -/
def routed (route : Array Nat) (x : Assignment) (i : Nat) : Rat :=
  match route[i]? with
  | none => 0
  | some j => x j

def letter (b : Book) (route : Array Nat) (i : Nat) : Word :=
  match route[i]? with
  | none => .int 0
  | some j => varWord b j

theorem letter_value (b : Book) (route : Array Nat) (x : Assignment) (i : Nat) :
    (letter b route i).value b x=routed route x i := by
  unfold letter routed
  split
  · rfl
  · exact variable_value ..

def getWord (xs : Array Word) (i : Nat) : Word := xs[i]?.getD (.int 0)

theorem getWord_value (b : Book) (x : Assignment) (xs : Array Word) (i : Nat) :
    (getWord xs i).value b x=read (xs.map (fun w=>w.value b x)) i := by
  simp only [getWord,CircuitTransport.read,Array.getElem?_map]
  cases xs[i]? <;> rfl

def copied (b : Book) (route : Array Nat) (out : Array Word) : Op → Word
  | .var i => letter b route i
  | .int c => integer b c
  | .add i j => plus b (getWord out i) (getWord out j)
  | .mul i j => times b (getWord out i) (getWord out j)

theorem copied_value (b : Book) (route : Array Nat) (x : Assignment) (out : Array Word) (op : Op) :
    (copied b route out op).value b x =
      op.value (routed route x) (read (out.map (fun w=>w.value b x))) := by
  cases op <;> simp only [copied,Op.value,letter_value,integer_value,plus_value,times_value,getWord_value]

def renameOps (b : Book) (route : Array Nat) : List Op → Array Word → Array Word
  | [],out => out
  | op::tail,out => renameOps b route tail (out.push (copied b route out op))

theorem renameOps_value (b : Book) (route : Array Nat) (x : Assignment) (ops : List Op) (out : Array Word) :
    (renameOps b route ops out).map (fun w=>w.value b x) =
       execute (routed route x) ops (out.map (fun w=>w.value b x)) := by
  induction ops generalizing out with
  | nil => rfl
  | cons op tail ih => rw [renameOps,execute,ih,Array.map_push,copied_value]

theorem renamed_reference (b : Book) (route : Array Nat) (x : Assignment) (ops : List Op) (i : Nat) :
    (getWord (renameOps b route ops #[]) i).value b x=valueAt ops (routed route x) i := by
  rw [getWord_value,renameOps_value]
  simp [valueAt]

inductive Frame | common | first | second | third | scalar
  deriving Inhabited, DecidableEq, BEq, Repr

/-- Each entry takes one of the seven source families to its own coordinates. -/
structure Route where
  family : Nat
  frame : Frame
  slots : Array Nat
  deriving Inhabited

abbrev Families := Array (List Op)
abbrev Routes := Array Route

structure Ref where
  cell : Nat
  node : Nat
  origin : Bool
  deriving Inhabited, DecidableEq, BEq, Repr

def Ref.index (r : Ref) (ops : List Op) : Nat := if r.origin then zeroIndex ops r.node else r.node
abbrev Words := Array (Array Word)

def rowValue (fs : Families) (rs : Routes) (x : Assignment) (r : Ref) : Rat :=
  let c:=rs[r.cell]!
  valueAt (fs[c.family]!) (routed c.slots x) (r.index (fs[c.family]!))

def tables (b : Book) (fs : Families) (rs : Routes) : Words :=
  rs.map fun c=>renameOps b c.slots (fs[c.family]!) #[]

def fromTables (b : Book) (fs : Families) (rs : Routes) (ws : Words) (r : Ref) : Word :=
  let index:=r.index (fs[(rs[r.cell]!).family]!)
  match ws[r.cell]? with
  | some a => getWord a index
  | none =>
    let c:=rs[r.cell]!
    getWord (renameOps b c.slots (fs[c.family]!) #[]) index

theorem row_value (b : Book) (fs : Families) (rs : Routes) (x : Assignment) (r : Ref) :
    (fromTables b fs rs (tables b fs rs) r).value b x = rowValue fs rs x r := by
  unfold fromTables tables rowValue
  rw [Array.getElem?_map]
  cases h : rs[r.cell]? with
  | none => exact renamed_reference ..
  | some route =>
    simp only [Option.map_some]
    have e : rs[r.cell]! = route := by
      rw [getElem!_def, h]
    rw [e]
    exact renamed_reference ..

end IndependentIndices
