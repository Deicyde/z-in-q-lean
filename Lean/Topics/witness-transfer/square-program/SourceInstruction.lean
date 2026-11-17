import SourceCheck
namespace SquareProgram
open CircuitTransport IndependentIndices

private theorem keeps (rows : List Row) (ops : List Op) (s : State) (j : Nat) (old : j<s.code.size) :
    (validate rows ops s).code[j]?=s.code[j]? := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih =>
    let v:=safeOp rows s o
    rw [validate,ih _ (by change j<(s.code.push v).size;simp;omega)]
    change (s.code.push v)[j]?=s.code[j]?
    rw [Array.getElem?_push,if_neg (by omega)]

private theorem read_unconstrained (rows : List Row) (raw : List Op) (s : State) (i : Nat) {op : Op}
    (absent : ∀ f n p, Row.inherit f n p∈rows → n≠s.code.size+i) (look : raw[i]?=some op) :
    (validate rows raw s).code[s.code.size+i]?=some op := by
  induction raw generalizing s i with
  | nil => simp at look
  | cons head rest ih =>
    cases i with
    | zero =>
      have eq : head=op := by simpa using look
      subst head
      have ok : rows.all (required s.code.size (predict s op))=true := by
        apply List.all_eq_true.mpr
        intro r mem
        cases r with
        | replace492 => rfl
        | inherit f n p =>
          have ne : n≠s.code.size := by simpa using absent f n p mem
          simp [required,ne]
      have hx : safeOp rows s op=op := if_pos ok
      rw [Nat.add_zero,validate,keeps rows rest _ _ (by change s.code.size<(s.code.push _).size;simp)]
      change (s.code.push (safeOp rows s op))[s.code.size]?=some op
      rw [hx,Array.getElem?_push,if_pos rfl]
    | succ k =>
      have a : (sourceStep rows s head).code.size=s.code.size+1 := by simp [sourceStep]
      have b : (sourceStep rows s head).code.size+k=s.code.size+(k+1) := by omega
      rw [validate,←b]
      exact ih _ k (fun f n p mem=>by rw [b];exact absent f n p mem) (by simpa using look)

theorem untouched (rows : List Row) (raw : List Op) (i : Nat) {op : Op}
    (noConstraint : ∀ f n p,Row.inherit f n p∈rows → n≠i) (look : raw[i]?=some op) :
    (checkedSource rows raw)[i]?=some op := by
  have sz : initial.code.size+i=i := by simp [initial]
  have h:=read_unconstrained rows raw initial i (by rw [sz];exact noConstraint) look
  rw [sz] at h
  simpa only [checkedSource,Array.getElem?_toList] using h

private theorem cat_run {α : Type} (f : Op→(Nat→α)→α) (z : α) (p q : List Op) (a : Array α) :
    run f z (p++q) a=run f z q (run f z p a) := by
  induction p generalizing a with
  | nil => rfl
  | cons o t ih => exact ih _

private theorem len_run {α : Type} (f : Op→(Nat→α)→α) (z : α) (p : List Op) (a : Array α) :
    (run f z p a).size=a.size+p.length := by
  induction p generalizing a with
  | nil => simp [run]
  | cons o t ih => rw [run,ih];simp;omega

private theorem keeps_run {α : Type} (f : Op→(Nat→α)→α) (z : α) (p : List Op) {i : Nat}
    (a : Array α) (hi : i<a.size) : getA z (run f z p a) i=getA z a i := by
  induction p generalizing a with
  | nil => rfl
  | cons o t ih =>
    rw [run,ih _ (by simp;omega)]
    simp only [getA,Array.getElem?_push,if_neg (show i≠a.size by omega)]

private theorem split_source {ops : List Op} {i : Nat} {o : Op} (h : ops[i]?=some o) :
    ∃ p q : List Op, ops=p++o::q ∧ p.length=i := by
  induction ops generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => have e : a=o := by simpa using h
              exact ⟨[],t,by simp [e]⟩
    | succ n =>
      obtain ⟨p,q,he,hn⟩:=ih (by simpa using h)
      refine ⟨a::p,q,?_,?_⟩
      · rw [he];rfl
      · simp [hn]

/-- An arbitrary certified earlier instruction in the pair-valued execution. -/
theorem pair_instruction {ops : List Op} {i : Nat} {o : Op} (look : ops[i]?=some o)
    (safe : o.safe i) (d : Rat) (x : Assignment) :
    valueQ ops d x i=stepQ d x o (valueQ ops d x) := by
  obtain ⟨p,q,rfl,rfl⟩:=split_source look
  let f:=stepQ d x
  let a:=run f zero p #[]
  have len : a.size=p.length := by simp [a,len_run]
  have before (j : Nat) (hj : j<p.length) : valueQ (p++o::q) d x j=getA zero a j := by
    unfold valueQ
    rw [cat_run]
    exact keeps_run f zero (o::q) a (by rw [len];exact hj)
  have same : valueQ (p++o::q) d x p.length=f o (getA zero a) := by
    unfold valueQ;rw [cat_run,run]
    have keep:=keeps_run f zero q (a.push (f o (getA zero a))) (i:=p.length) (by simp;omega)
    rw [keep]
    unfold getA;rw [Array.getElem?_push,len,if_pos rfl];rfl
  rw [same]
  cases o with
  | int => rfl
  | var => rfl
  | add i j => change addQ _ _=addQ _ _;rw [before i safe.1,before j safe.2]
  | mul i j => change mulQ _ _ _=mulQ _ _ _;rw [before i safe.1,before j safe.2]
end SquareProgram
