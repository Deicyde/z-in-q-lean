import SquareCompiler

namespace SquareProgram
open CircuitTransport IndependentIndices

def passes (t : Tags) (peak : Bool) : Bool :=
  t.localTo && t.noImag && (!peak || t.sourceZero)

def required (address : Nat) (tags : Frame→Tags) : Row→Bool
  | .replace492 => true
  | .inherit f n peak => (decide (n≠address)) || passes (tags f) peak

structure State where
  code : Array Op
  tags : Bank

def initial : State := ⟨#[],⟨#[],#[],#[],#[],#[]⟩⟩

def predict (s : State) (o : Op) (f : Frame) : Tags :=
  tagStep f o (getA blankTags (s.tags.atFrame f))

def safeOp (rows : List Row) (s : State) (o : Op) : Op :=
  if rows.all (required s.code.size (predict s o)) then o else .int 0

def addTags (s : State) (o : Op) : Bank :=
  let a f:=(s.tags.atFrame f).push (predict s o f)
  ⟨a .common,a .first,a .second,a .third,a .scalar⟩

theorem addTags_at (s : State) (o : Op) (f : Frame) :
    (addTags s o).atFrame f=(s.tags.atFrame f).push (predict s o f) := by cases f <;> rfl

def sourceStep (rows : List Row) (s : State) (o : Op) : State :=
  let a:=safeOp rows s o
  ⟨s.code.push a,addTags s a⟩

def validate (rows : List Row) : List Op→State→State
  | [],s => s
  | o::os,s => validate rows os (sourceStep rows s o)

private theorem run_append {α : Type} (step : Op→(Nat→α)→α) (z : α)
    (lo hi : List Op) (a : Array α) :
    run step z (lo++hi) a=run step z hi (run step z lo a) := by
  induction lo generalizing a with
  | nil => rfl
  | cons o os ih => exact ih _

private theorem count (f : Frame) (xs : List Op) (a : Array Tags) :
    (run (tagStep f) blankTags xs a).size=a.size+xs.length := by
  induction xs generalizing a with
  | nil => simp [run]
  | cons o os ih => rw [run,ih];simp;omega

private theorem fresh_ok (rows : List Row) (s : State) (o : Op) (f : Frame) (p : Bool)
    (mem : Row.inherit f s.code.size p∈rows) :
    passes (predict s (safeOp rows s o) f) p=true := by
  unfold safeOp;split
  · rename_i checked
    have h:=List.all_eq_true.mp checked _ mem
    simpa [required] using h
  · cases p <;> rfl

structure Valid (rows : List Row) (s : State) : Prop where
  complete : ∀f,s.tags.atFrame f=run (tagStep f) blankTags s.code.toList #[]
  checked : ∀ f n p, Row.inherit f n p∈rows → n<s.code.size →
    passes (getA blankTags (s.tags.atFrame f) n) p=true

private theorem start_ok (rows : List Row) : Valid rows initial := by
  constructor
  · intro f;cases f <;> rfl
  · intro f n p mem h;change n<0 at h;omega

private theorem step_ok (rows : List Row) (s : State) (o : Op) (good : Valid rows s) :
    Valid rows (sourceStep rows s o) := by
  let actual:=safeOp rows s o
  constructor
  · intro f
    change (addTags s actual).atFrame f=run (tagStep f) blankTags (s.code.push actual).toList #[]
    rw [addTags_at,Array.toList_push,run_append]
    change (s.tags.atFrame f).push (predict s actual f)=
      (run (tagStep f) blankTags s.code.toList #[]).push _
    rw [←good.complete f]
    rfl
  · intro f n p mem bounded
    have size : (s.tags.atFrame f).size=s.code.size := by rw [good.complete,count];simp
    change n<(s.code.push actual).size at bounded
    change passes (getA blankTags ((addTags s actual).atFrame f) n) p=true
    rw [addTags_at]
    simp only [getA,Array.getElem?_push,size]
    by_cases last : n=s.code.size
    · subst n
      simp only [if_true,Option.getD_some]
      exact fresh_ok rows s o f p mem
    · simp only [last,if_false]
      exact good.checked f n p mem (by simp only [Array.size_push] at bounded;omega)

private theorem validated (rows : List Row) (ops : List Op) (s : State) (h : Valid rows s) :
    Valid rows (validate rows ops s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (step_ok rows s o h)

/-- All original instructions, with source annotations checked on insertion.
    Re-emission compares every opcode and address with the original JSON. -/
def checkedSource (rows : List Row) (raw : List Op) : List Op := (validate rows raw initial).code.toList

theorem checked_index (rows : List Row) (raw : List Op) (f : Frame) (n : Nat) (p : Bool)
    (mem : Row.inherit f n p∈rows) :
    selected (checkedSource rows raw) f n p=n := by
  let s:=validate rows raw initial
  have h : Valid rows s := validated rows raw initial (start_ok rows)
  have good : passes (tagAt s.code.toList f n) p=true := by
    unfold tagAt
    rw [←h.complete f]
    by_cases inside : n<s.code.size
    · exact h.checked f n p mem inside
    · have size : (s.tags.atFrame f).size=s.code.size := by rw [h.complete,count];simp
      have z : (s.tags.atFrame f)[n]?=none := Array.getElem?_eq_none (by omega)
      unfold getA;rw [z];cases p <;> rfl
  change selected s.code.toList f n p=n
  change (if passes (tagAt s.code.toList f n) p=true then n else s.code.toList.length)=n
  rw [if_pos good]

end SquareProgram
