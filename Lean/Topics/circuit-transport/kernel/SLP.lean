import Std

namespace CircuitTransport

inductive Op where
  | var (slot : Nat)
  | int (coefficient : Int)
  | add (left right : Nat)
  | mul (left right : Nat)
  deriving DecidableEq, BEq, Hashable, Repr

abbrev Assignment := Nat → Rat

def Op.value (x env : Assignment) : Op → Rat
  | .var i => x i
  | .int c => c
  | .add a b => env a+env b
  | .mul a b => env a*env b

def Op.safe (i : Nat) : Op→Prop
  | .var _ | .int _ => True
  | .add a b | .mul a b => a<i ∧ b<i

instance (i) (op : Op) : Decidable (op.safe i) := by cases op <;> unfold Op.safe <;> infer_instance

def read (a : Array Rat) (i : Nat) : Rat := a[i]?.getD 0

def execute (x : Assignment) : List Op → Array Rat → Array Rat
  | [], a => a
  | op::rest,a => execute x rest (a.push (op.value x (read a)))

def valueAt (ops : List Op) (x : Assignment) (i : Nat) : Rat := read (execute x ops #[]) i

private theorem exec_size (x : Assignment) (ops : List Op) (a : Array Rat) :
    (execute x ops a).size = a.size+ops.length := by
  induction ops generalizing a with
  | nil => simp [execute]
  | cons h t ih => rw [execute,ih]; simp;omega

private theorem exec_append (x : Assignment) (p q : List Op) (a : Array Rat) :
    execute x (p++q) a = execute x q (execute x p a) := by
  induction p generalizing a with
  | nil => rfl
  | cons h t ih => exact ih _

private theorem exec_keeps (x : Assignment) (p : List Op) (a : Array Rat) {i : Nat} (h : i<a.size) :
    read (execute x p a) i = read a i := by
  induction p generalizing a with
  | nil => rfl
  | cons op t ih =>
    rw [execute,ih _ (by simp;omega)]
    simp [read,Array.getElem?_push,h,show i≠a.size by omega]

theorem append_keeps (x : Assignment) (p q : List Op) {i : Nat} (h : i<p.length) :
    valueAt (p++q) x i=valueAt p x i := by
  unfold valueAt;rw [exec_append]; apply exec_keeps
  simpa [exec_size] using h

theorem missing_zero (x : Assignment) (p : List Op) (i : Nat) (out : p.length≤i) : valueAt p x i=0 := by
  unfold valueAt read
  have h : (execute x p #[]).size≤i := by simpa [exec_size] using out
  rw [Array.getElem?_eq_none h];rfl

theorem last_value (x : Assignment) (p : List Op) (op : Op) :
    valueAt (p++[op]) x p.length=op.value x (valueAt p x) := by
  unfold valueAt
  rw [exec_append,execute,execute]
  have len : (execute x p #[]).size=p.length := by simp [exec_size]
  change read ((execute x p #[]).push _) p.length=_
  rw [←len]; simp [read]; rfl

private theorem splitAt {ops : List Op} {i : Nat} {op : Op} (h : ops[i]?=some op) :
    ∃ pre tail : List Op, ops=pre++op::tail ∧ pre.length=i := by
  induction ops generalizing i with
  | nil => simp at h
  | cons head rest ih =>
    cases i with
    | zero =>
      have eq : head=op := by simpa using h
      subst head; exact ⟨[],rest,rfl,rfl⟩
    | succ n =>
      obtain ⟨a,b,eq,len⟩ := ih (by simpa using h)
      refine ⟨head::a,b,?_,?_⟩
      · rw [eq];rfl
      · simp [len]

theorem instruction {ops : List Op} {i : Nat} {op : Op} (look : ops[i]?=some op)
    (safe : op.safe i) (x : Assignment) : valueAt ops x i=op.value x (valueAt ops x) := by
  obtain ⟨a,b,rfl,rfl⟩ := splitAt look
  have lhs : valueAt (a++op::b) x a.length=op.value x (valueAt a x) := by
    rw [show a++op::b=(a++[op])++b by simp]
    rw [append_keeps _ _ _ (by simp),last_value]
  rw [lhs]
  cases op with
  | var i => rfl
  | int c => rfl
  | add i j => change _+_= _+_;rw [append_keeps _ a _ safe.1,append_keeps _ a _ safe.2]
  | mul i j => change _*_= _*_;rw [append_keeps _ a _ safe.1,append_keeps _ a _ safe.2]

structure Program where
  nodes : List Op
  ordinary : Nat
  marked : Nat

def Program.eval (p : Program) (marked : Bool) (x : Assignment) : Rat :=
  valueAt p.nodes x (if marked then p.marked else p.ordinary)

end CircuitTransport
