import RenamedTape

namespace IndependentIndices
open CircuitTransport

inductive Tree where
  | leaf (r : Ref)
  | sum (a b : Tree)
  deriving Repr, Inhabited

def Tree.refs : Tree → List Ref
  | .leaf r => [r]
  | .sum a b => a.refs++b.refs

def Tree.sos (f : Ref→Rat) : Tree→Rat
  | .leaf r => f r * f r
  | .sum a b => a.sos f+b.sos f

def Tree.word (b : Book) (resolve : Ref→Word) : Tree→Word
  | .leaf r => times b (resolve r) (resolve r)
  | .sum a c => plus b (a.word b resolve) (c.word b resolve)

theorem Tree.word_value (b : Book) (x : Assignment) (resolve : Ref→Word) (t : Tree) :
    (t.word b resolve).value b x=t.sos (fun r=>(resolve r).value b x) := by
  induction t with
  | leaf => exact times_value ..
  | sum a c ha hc => simp only [Tree.word,Tree.sos,plus_value,ha,hc]

private theorem sq_nonneg (a : Rat) : 0≤a*a := by
  rcases Rat.nonneg_total a with h|h
  · exact Rat.mul_nonneg h h
  · have p:=Rat.mul_nonneg h h;grobner

theorem Tree.nonnegative (t : Tree) (f : Ref→Rat) : 0≤t.sos f := by
  induction t with
  | leaf => exact sq_nonneg _
  | sum a c ha hc => exact Rat.add_nonneg ha hc

theorem Tree.sos_zero (t : Tree) (f : Ref→Rat) : t.sos f=0 ↔ ∀r∈t.refs,f r=0 := by
  induction t with
  | leaf r =>
    simp only [Tree.sos,Tree.refs,List.mem_singleton,forall_eq,Rat.mul_eq_zero,or_self]
  | sum a c ha hc =>
    simp only [Tree.sos,Tree.refs,List.forall_mem_append,←ha,←hc]
    have h:=a.nonnegative f;have l:=c.nonnegative f;constructor <;> grind

structure Shape where
  high : Tree
  low : Tree

def active (s : Shape) (marked : Bool) (x : Assignment) : List Ref :=
  if marked=true ∧ x 1=0 then s.high.refs else s.high.refs++s.low.refs

def conditions (s : Shape) (fs : Families) (rs : Routes) (marked : Bool) (x : Assignment) : Prop :=
  ∀ r∈active s marked x, rowValue fs rs x r=0

def frameConditions (s : Shape) (fs : Families) (rs : Routes) (marked : Bool) (x : Assignment) (frame : Frame) : Prop :=
  ∀ r∈active s marked x, (rs[r.cell]!).frame=frame → rowValue fs rs x r=0

theorem grouped (s : Shape) (fs : Families) (rs : Routes) (marked : Bool) (x : Assignment) :
    conditions s fs rs marked x ↔
    frameConditions s fs rs marked x .common ∧ frameConditions s fs rs marked x .first ∧
    frameConditions s fs rs marked x .second ∧ frameConditions s fs rs marked x .third ∧
    frameConditions s fs rs marked x .scalar := by
  constructor
  · intro h;exact ⟨fun r hr _=>h r hr,fun r hr _=>h r hr,fun r hr _=>h r hr,
                     fun r hr _=>h r hr,fun r hr _=>h r hr⟩
  · rintro ⟨h0,h1,h2,h3,hs⟩ r hr
    cases h : (rs[r.cell]!).frame with
    | common => exact h0 r hr h
    | first => exact h1 r hr h
    | second => exact h2 r hr h
    | third => exact h3 r hr h
    | scalar => exact hs r hr h

def build (seed : Array Op) (fs : Families) (rs : Routes) (s : Shape) : Program :=
  let b:=Book.make seed
  let table:=tables b fs rs
  let get:=fromTables b fs rs table
  let high:=s.high.word b get
  let low:=s.low.word b get
  let X:=varWord b 1
  finish b (plus b high low) (plus b high (times b (times b X X) low))

/-- Pointwise numerical evaluation on the two signed sums, including at x₁=0. -/
theorem outputs (seed : Array Op) (fs : Families) (rs : Routes) (s : Shape) (x : Assignment) :
    let f:=rowValue fs rs x
    ((build seed fs rs s).eval false x=s.high.sos f+s.low.sos f) ∧
    ((build seed fs rs s).eval true x=s.high.sos f+(x 1*x 1)*s.low.sos f) := by
  let b:=Book.make seed
  let fetch:=fromTables b fs rs (tables b fs rs)
  let h:=s.high.word b fetch
  let l:=s.low.word b fetch
  have valid:=finish_value b (plus b h l) (plus b h (times b (times b (varWord b 1) (varWord b 1)) l)) x
  have eq : (fun r=>(fetch r).value b x)=rowValue fs rs x := funext (row_value b fs rs x)
  simpa only [build,b,h,l,fetch,plus_value,times_value,variable_value,Tree.word_value,eq] using valid

theorem pointwise (seed : Array Op) (fs : Families) (rs : Routes) (s : Shape) (marked : Bool) (x : Assignment) :
    (build seed fs rs s).eval marked x=0 ↔ conditions s fs rs marked x := by
  let f:=rowValue fs rs x
  have h:=s.high.nonnegative f
  have l:=s.low.nonnegative f
  have q:=sq_nonneg (x 1)
  have ql:=Rat.mul_nonneg q l
  have H:=s.high.sos_zero f
  have L:=s.low.sos_zero f
  obtain ⟨eo,em⟩:=outputs seed fs rs s x
  cases marked with
  | false =>
    rw [eo];simp only [conditions,active,Bool.false_eq_true,false_and,if_false,List.forall_mem_append]
    change s.high.sos f+s.low.sos f=0 ↔ _
    rw [←H,←L];constructor <;> grind
  | true =>
    rw [em];simp only [conditions,active,true_and]
    by_cases zero : x 1=0
    · rw [if_pos zero,zero];simp only [Rat.zero_mul,Rat.add_zero];exact H
    · rw [if_neg zero,List.forall_mem_append,←H,←L]
      change s.high.sos f+(x 1*x 1)*s.low.sos f=0 ↔ _
      constructor
      · intro e
        have hh : s.high.sos f=0 := by grind
        have k : (x 1*x 1)*s.low.sos f=0 := by grind
        exact ⟨hh,(Rat.mul_eq_zero.mp k).resolve_left (fun h=>(Rat.mul_eq_zero.mp h).elim zero zero)⟩
      · rintro ⟨hh,ll⟩;rw [hh,ll];grobner

end IndependentIndices
