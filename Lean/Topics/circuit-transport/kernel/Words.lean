import SLP
namespace CircuitTransport

structure Book where
  ops : Array Op
  index : Std.HashMap Op Nat

def Book.make (ops : Array Op) : Book :=
  ⟨ops,ops.toList.zipIdx.foldl (fun m p => m.insert p.1 p.2) {}⟩

inductive Word where
  | ref (index : Nat)
  | int (c : Int)
  | var (i : Nat)
  | add (left right : Word)
  | mul (left right : Word)
  deriving Repr

def Word.value (b : Book) (x : Assignment) : Word→Rat
  | .ref i => valueAt b.ops.toList x i
  | .int n => n
  | .var i => x i
  | .add a c => a.value b x+c.value b x
  | .mul a c => a.value b x*c.value b x

/-- The hash map may contain arbitrary guesses. Check the underlying instruction and its dependencies. -/
def reuse (b : Book) (op : Op) (fallback : Word) : Word :=
  match b.index[op]? with
  | none => fallback
  | some i => if b.ops[i]?=some op ∧ op.safe i then .ref i else fallback

theorem reuse_value (b : Book) (x : Assignment) (op : Op) (w : Word)
    (eq : w.value b x=op.value x (valueAt b.ops.toList x)) : (reuse b op w).value b x=w.value b x := by
  unfold reuse;split
  · rfl
  · split
    · rename_i ok; exact (instruction (by simpa using ok.1) ok.2 x).trans eq.symm
    · rfl

def integer (b : Book) (n : Int) := reuse b (.int n) (.int n)
def varWord (b : Book) (i : Nat) := reuse b (.var i) (.var i)
theorem integer_value (b : Book) (x : Assignment) (n : Int) : (integer b n).value b x=n :=
  reuse_value b x _ _ rfl
theorem variable_value (b : Book) (x : Assignment) (i : Nat) : (varWord b i).value b x=x i :=
  reuse_value b x _ _ rfl

def Word.number? (b : Book) : Word→Option Int
  | .int n => some n
  | .ref i => match b.ops[i]? with | some (.int n) => some n | _ => none
  | _ => none

theorem number_value {w : Word} {b : Book} {n : Int} (h : w.number? b=some n) (x : Assignment) : w.value b x=n := by
  cases w with
  | int c =>
    have eq : c=n := by simpa [Word.number?] using h
    exact congrArg (fun i : Int => (i:Rat)) eq
  | ref i =>
    cases he : b.ops[i]? with
    | none => simp [Word.number?,he] at h
    | some op =>
      cases op with
      | int c =>
        have eq : c=n := by simpa [Word.number?,he] using h
        subst c; exact instruction (by simpa using he) (by trivial : (Op.int n).safe i) x
      | _ => simp [Word.number?,he] at h
  | _ => simp [Word.number?] at h

inductive Kind | add | mul

def Kind.op : Kind→Nat→Nat→Op | .add => Op.add | .mul => Op.mul
def Kind.tree : Kind→Word→Word→Word | .add => Word.add | .mul => Word.mul
def Kind.act : Kind→Rat→Rat→Rat | .add => (·+·) | .mul => (·*·)

private theorem tree_value (b : Book) (x : Assignment) (k : Kind) (u v : Word) :
    (k.tree u v).value b x=k.act (u.value b x) (v.value b x) := by cases k <;> rfl

def combine (b : Book) (k : Kind) (u v : Word) : Word :=
  match u,v with
  | .ref i,.ref j =>
    let node := if i≤j then k.op i j else k.op j i
    reuse b node (k.tree (.ref i) (.ref j))
  | _,_ => k.tree u v

theorem combine_value (b : Book) (x : Assignment) (k : Kind) (u v : Word) :
    (combine b k u v).value b x=k.act (u.value b x) (v.value b x) := by
  unfold combine;split
  · rename_i i j
    apply Eq.trans (reuse_value b x _ _ ?_) (tree_value _ _ _ _ _)
    split <;> cases k <;> simp only [Kind.tree,Kind.op,Word.value,Op.value] <;> grobner
  · exact tree_value _ _ _ _ _

def plus (b : Book) (u v : Word) : Word :=
  match u.number? b,v.number? b with
  | some n,some m => integer b (n+m)
  | some n,none => if n=0 then v else combine b .add u v
  | none,some m => if m=0 then u else combine b .add u v
  | none,none => combine b .add u v

theorem plus_value (b : Book) (x : Assignment) (u v : Word) :
    (plus b u v).value b x=u.value b x+v.value b x := by
  unfold plus;split
  · rename_i n m hn hm; rw [integer_value,number_value hn,number_value hm,Rat.intCast_add]
  · rename_i n hn _;split
    · rename_i eq;rw [number_value hn,eq,Rat.intCast_zero,Rat.zero_add]
    · exact combine_value _ _ .add _ _
  · rename_i m _ hm;split
    · rename_i eq;rw [number_value hm,eq,Rat.intCast_zero,Rat.add_zero]
    · exact combine_value _ _ .add _ _
  · exact combine_value _ _ .add _ _

def special (b : Book) (n : Int) (other normal : Word) :=
  if n=0 then integer b 0 else if n=1 then other else normal

private theorem special_value (b : Book) (x : Assignment) (n : Int) (u v : Word)
    (normal : v.value b x=(n:Rat)*u.value b x) : (special b n u v).value b x=(n:Rat)*u.value b x := by
  unfold special;split
  · rename_i h;rw [integer_value,h,Rat.intCast_zero,Rat.zero_mul]
  · split
    · rename_i h; rw [h,Rat.intCast_one,Rat.one_mul]
    · exact normal

def times (b : Book) (u v : Word) : Word :=
  match u.number? b,v.number? b with
  | some n,some m => integer b (n*m)
  | some n,none => special b n v (combine b .mul u v)
  | none,some m => special b m u (combine b .mul u v)
  | none,none => combine b .mul u v

theorem times_value (b : Book) (x : Assignment) (u v : Word) :
    (times b u v).value b x=u.value b x*v.value b x := by
  unfold times;split
  · rename_i n m hn hm;rw [integer_value,number_value hn,number_value hm,Rat.intCast_mul]
  · rename_i n hn _;rw [number_value hn];apply special_value
    exact (combine_value b x .mul u v).trans (by rw [number_value hn];rfl)
  · rename_i m _ hm;rw [number_value hm,Rat.mul_comm];apply special_value
    exact (combine_value b x .mul u v).trans (by change u.value b x*v.value b x=_;rw [number_value hm,Rat.mul_comm])
  · exact combine_value _ _ .mul _ _

end CircuitTransport
