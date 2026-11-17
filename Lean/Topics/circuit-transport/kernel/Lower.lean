import Words
namespace CircuitTransport

structure Emitted where
  code : List Op
  index : Nat

private def push (p : List Op) (op : Op) : Emitted := ⟨p++[op],p.length⟩

/-- A missed cache entry is compiled as an ordinary operation. Only final results are lowered. -/
def emit (b : Book) (p : List Op) : Word→Emitted
  | .int k => push p (.int k)
  | .var i => push p (.var i)
  | .ref i => if i<b.ops.size then ⟨p,i⟩ else push p (.int 0)
  | .add a c =>
    let l := emit b p a
    let r := emit b l.code c
    push r.code (.add l.index r.index)
  | .mul a c =>
    let l := emit b p a
    let r := emit b l.code c
    push r.code (.mul l.index r.index)

def Ext (p q : List Op) : Prop := ∃ tail, q=p++tail

private theorem reflExt (p : List Op) : Ext p p := ⟨[],by simp⟩
private theorem transExt {p q r : List Op} (h : Ext p q) (k : Ext q r) : Ext p r := by
  obtain ⟨a,rfl⟩ := h;obtain ⟨b,rfl⟩ := k; exact ⟨a++b,by simp⟩
private theorem pushExt (p : List Op) (op : Op) : Ext p (push p op).code := ⟨[op],rfl⟩
private theorem lengthExt {p q : List Op} (ext : Ext p q) : p.length≤q.length := by
  obtain ⟨a,rfl⟩ := ext;simp
private theorem extKeeps {p q : List Op} (x : Assignment) (h : Ext p q) {i} (bound : i<p.length) :
    valueAt q x i=valueAt p x i := by obtain ⟨a,rfl⟩ := h; exact append_keeps _ _ _ bound

structure Correct (b : Book) (p : List Op) (word : Word) (out : Emitted) : Prop where
  extended : Ext p out.code
  bound : out.index<out.code.length
  value : ∀ x, valueAt out.code x out.index=word.value b x

private theorem binaryCorrect (b : Book) (p : List Op) (a c : Word) (l r : Emitted)
    (hl : Correct b p a l) (hr : Correct b l.code c r) (k : Kind) :
    Correct b p (k.tree a c) (push r.code (k.op l.index r.index)) := by
  refine ⟨transExt hl.extended (transExt hr.extended (pushExt _ _)),by simp [push],?_⟩
  intro x
  change valueAt (r.code++[k.op l.index r.index]) x r.code.length=_
  rw [last_value]
  have left := (extKeeps x hr.extended hl.bound).trans (hl.value x)
  cases k <;> simp only [Kind.tree,Kind.op,Op.value,Word.value,left,hr.value x]

theorem emit_correct (b : Book) (p : List Op) (prev : Ext b.ops.toList p) (w : Word) : Correct b p w (emit b p w) := by
  induction w generalizing p with
  | int k => exact ⟨pushExt _ _,by simp [emit,push],fun x => last_value x p (.int k)⟩
  | var i => exact ⟨pushExt _ _,by simp [emit,push],fun x => last_value x p (.var i)⟩
  | ref i =>
    by_cases hi : i<b.ops.size
    · rw [show emit b p (.ref i)=⟨p,i⟩ from if_pos hi]
      have bound : i<b.ops.toList.length := by simpa using hi
      exact ⟨reflExt _,Nat.lt_of_lt_of_le bound (lengthExt prev),fun x => extKeeps x prev bound⟩
    · rw [show emit b p (.ref i)=push p (.int 0) from if_neg hi]
      refine ⟨pushExt _ _,by simp [push],?_⟩
      intro x;change valueAt (p++[.int 0]) x p.length=valueAt b.ops.toList x i
      rw [last_value,missing_zero _ _ _ (by simp;omega)];rfl
  | add a c ia ic =>
    have hl := ia p prev
    exact binaryCorrect b p a c _ _ hl (ic _ (transExt prev hl.extended)) .add
  | mul a c ia ic =>
    have hl := ia p prev
    exact binaryCorrect b p a c _ _ hl (ic _ (transExt prev hl.extended)) .mul

def finish (b : Book) (ordinary marked : Word) : Program :=
  let a := emit b b.ops.toList ordinary
  let m := emit b a.code marked
  ⟨m.code,a.index,m.index⟩

theorem finish_value (b : Book) (ordinary marked : Word) (x : Assignment) :
    (finish b ordinary marked).eval false x=ordinary.value b x ∧
    (finish b ordinary marked).eval true x=marked.value b x := by
  let a := emit b b.ops.toList ordinary
  let m := emit b a.code marked
  have ha : Correct b b.ops.toList ordinary a := emit_correct b _ (reflExt _) _
  have hm : Correct b a.code marked m := emit_correct b _ ha.extended _
  exact ⟨(extKeeps x hm.extended ha.bound).trans (ha.value x),hm.value x⟩

end CircuitTransport
