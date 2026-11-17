import GateWords

namespace SquareProgram
open CircuitTransport IndependentIndices

structure Bank where
  common : Array Tags
  first : Array Tags
  second : Array Tags
  third : Array Tags
  scalar : Array Tags

def Bank.atFrame (b : Bank) : Frame→Array Tags
  | .common => b.common
  | .first => b.first
  | .second => b.second
  | .third => b.third
  | .scalar => b.scalar

def bank (ops : List Op) : Bank :=
  let make f:=run (tagStep f) blankTags ops #[]
  ⟨make .common,make .first,make .second,make .third,make .scalar⟩

def guardedIndex (size : Nat) (tags : Bank) (f : Frame) (n : Nat) (peak : Bool) :=
  let a:=getA blankTags (tags.atFrame f) n
  if a.localTo && a.noImag && (!peak || a.sourceZero) then n else size

theorem guarded_eq (ops : List Op) (f : Frame) (n : Nat) (peak : Bool) :
    guardedIndex ops.length (bank ops) f n peak=selected ops f n peak := by cases f <;> rfl

def result (b : Book) (size : Nat) (tags : Bank) (ws : Array PairWord) : Row→Coeff
  | .replace492 => constant (correctedWord b)
  | .inherit f n p => (getA empty ws (guardedIndex size tags f n p)).re

def table (b : Book) (ops : List Op) := run (compileStep b (ySquareWord b)) empty ops #[]

theorem coeff_exact (b : Book) (ops : List Op) (r : Row) (x : Assignment) :
    coeffVal b x (result b ops.length (bank ops) (table b ops) r) = signedValue ops x r := by
  cases r with
  | replace492 =>
    change (correctedWord b).value b x / scale 0 = corrected x
    rw [corrected_value,scale_zero];grobner
  | inherit f n peak =>
    dsimp only [result,signedValue]
    rw [guarded_eq]
    have h:=congrArg PairQ.re (compiled_reference b x (ySquareWord b) ops (selected ops f n peak))
    rw [y2_value] at h
    exact h

theorem signed_numerator (b : Book) (ops : List Op) (r : Row) (x : Assignment) :
    let c:=result b ops.length (bank ops) (table b ops) r
    (c.num b).value b x=signedValue ops x r * scale c.exponent := by
  dsimp only
  rw [numerator,coeff_exact]

def squareSum (f : Row→Rat) : List Row→Rat
  | [] => 0
  | r::rs => f r*f r + squareSum f rs

def collect (b : Book) (w : Row→Word) (a : Word) : List Row→Word
  | [] => a
  | r::rs => collect b w (plus b a (times b (w r) (w r))) rs

theorem collect_value (b : Book) (x : Assignment) (w : Row→Word) (a : Word) (rows : List Row) :
    (collect b w a rows).value b x=a.value b x+squareSum (fun r=>(w r).value b x) rows := by
  induction rows generalizing a with
  | nil => simp [collect,squareSum,Rat.add_zero]
  | cons r rs ih => rw [collect,ih,plus_value,times_value,squareSum];grobner

private theorem square_nonneg (a : Rat) : 0≤a*a := by
  rcases Rat.nonneg_total a with h|h
  · exact Rat.mul_nonneg h h
  · have n:=Rat.mul_nonneg h h;grobner

theorem sum_nonneg (f : Row→Rat) (rs : List Row) : 0≤squareSum f rs := by
  induction rs with
  | nil => exact Rat.le_refl
  | cons r rs ih => exact Rat.add_nonneg (square_nonneg _) ih

theorem sum_zero (f : Row→Rat) (rs : List Row) : squareSum f rs=0 ↔ ∀r∈rs, f r=0 := by
  induction rs with
  | nil => simp [squareSum]
  | cons r rs ih =>
    simp only [squareSum,List.forall_mem_cons,←ih]
    have v:=square_nonneg (f r);have s:=sum_nonneg f rs
    constructor
    · intro h
      have sq : f r*f r=0 := by grind
      exact ⟨(Rat.mul_eq_zero.mp sq).elim id id,by grind⟩
    · rintro ⟨z,h⟩;rw [z,h];grobner

structure Shape where
  high : List Row
  low : List Row

def values (b : Book) (ops : List Op) (x : Assignment) (r : Row) : Rat :=
  ((result b ops.length (bank ops) (table b ops) r).num b).value b x

def form (s : Shape) (marked : Bool) (x : Assignment) (f : Row→Rat) :=
  squareSum f s.high+(if marked then x 1*x 1 else 1)*squareSum f s.low

def active (s : Shape) (m : Bool) (x : Assignment) :=
  if m=true ∧ x 1=0 then s.high else s.high++s.low

def compile (seed : Array Op) (ops : List Op) (s : Shape) : Program :=
  let b:=Book.make seed;let t:=bank ops;let w:=table b ops; let n:=ops.length
  let resolve r:=(result b n t w r).num b
  let h:=collect b resolve (integer b 0) s.high
  let low:=collect b resolve (integer b 0) s.low
  let input:=varWord b 1
  finish b (plus b h low) (plus b h (times b (times b input input) low))

theorem output (seed : Array Op) (ops : List Op) (s : Shape) (m : Bool) (x : Assignment) :
    (compile seed ops s).eval m x=form s m x (values (Book.make seed) ops x) := by
  let b:=Book.make seed
  let resolve r:=(result b ops.length (bank ops) (table b ops) r).num b
  let h:=collect b resolve (integer b 0) s.high
  let l:=collect b resolve (integer b 0) s.low
  have fin:=finish_value b (plus b h l) (plus b h (times b (times b (varWord b 1) (varWord b 1)) l)) x
  cases m with
  | false =>
    simpa only [compile,b,h,l,resolve,form,values,plus_value,collect_value,integer_value,Rat.intCast_zero,
      Rat.zero_add,Bool.false_eq_true,if_false,Rat.one_mul] using fin.1
  | true =>
    simpa only [compile,b,h,l,resolve,form,values,plus_value,times_value,variable_value,collect_value,
      integer_value,Rat.intCast_zero,Rat.zero_add,if_true] using fin.2

theorem form_zero (s : Shape) (m : Bool) (x : Assignment) (f : Row→Rat) :
    form s m x f=0 ↔ ∀r∈active s m x, f r=0 := by
  have hi:=sum_nonneg f s.high;have lo:=sum_nonneg f s.low
  have sq:=square_nonneg (x 1);have xl:=Rat.mul_nonneg sq lo
  cases m with
  | false =>
    simp only [form,active,Bool.false_eq_true,false_and,if_false,Rat.one_mul,List.forall_mem_append,←sum_zero]
    constructor <;> grind
  | true =>
    simp only [form,active,if_true,true_and]
    by_cases zero : x 1=0
    · rw [if_pos zero,zero,Rat.zero_mul,Rat.zero_mul,Rat.add_zero];exact sum_zero _ _
    · rw [if_neg zero,List.forall_mem_append,←sum_zero,←sum_zero]
      constructor
      · intro e
        have h : squareSum f s.high=0 := by grind
        have k : (x 1*x 1)*squareSum f s.low=0 := by grind
        exact ⟨h,(Rat.mul_eq_zero.mp k).resolve_left (fun z=>(Rat.mul_eq_zero.mp z).elim zero zero)⟩
      · rintro ⟨a,b⟩;rw [a,b];grobner

theorem pointwise (seed : Array Op) (ops : List Op) (s : Shape) (m : Bool) (x : Assignment) :
    (compile seed ops s).eval m x=0 ↔ ∀r∈active s m x,signedValue ops x r=0 := by
  rw [output,form_zero]
  have eq (r : Row) : values (Book.make seed) ops x r=0 ↔ signedValue ops x r=0 := by
    unfold values
    rw [signed_numerator]
    constructor
    · intro h;exact (Rat.mul_eq_zero.mp h).resolve_right (scale_ne _)
    · intro h;rw [h,Rat.zero_mul]
  exact ⟨fun h r hr=>(eq r).mp (h r hr),fun h r hr=>(eq r).mpr (h r hr)⟩

end SquareProgram
