import Compile
import PadeRecovery
namespace Physical130
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data CircuitTransport PhysicalProjection

def base (b : Book) (i : Nat) : Cell := ⟨varWord b (compactSlot i),1⟩

theorem base_along (b : Book) (y : Fin 130→Rat) : Along b (finiteLift y) (base b) (seed130 y) := by
  intro i; exact ⟨Nat.zero_lt_one,by simp [base,seed130,variable_value,Rat.one_mul]⟩

def timeRow : DBlock → Polynomial
  | .one => [⟨1,[]⟩,⟨-1,[32]⟩]
  | .two => [⟨1,[]⟩,⟨-4,[145]⟩]
  | .three => [⟨1,[]⟩,⟨-1,[32]⟩,⟨-32,[157]⟩]

theorem time_value (k : DBlock) (z : ProjectionDescent.Assignment) : value z (timeRow k)=k.t z := by
  cases k <;> simp [timeRow,DBlock.t,value,termValue,monomialValue] <;> grobner

def denMon (d : Nat→Nat) : List Nat→Nat
  | [] => 1 | i::t => d i * denMon d t

def denRow (d : Nat→Nat) : Polynomial→Nat
  | [] => 1 | t::ts => Nat.lcm (denMon d t.monomial) (denRow d ts)

def denRestore : List Pivot → (Nat→Nat) → (Nat→Nat)
  | [],d => d
  | p::ps,d => denRestore ps (fun i => if i=p.slot then denRow d (p.pre++p.post)*p.lead.natAbs else d i)

private theorem mon_den (env : Coords) (m : List Nat) : monDen env m=denMon (fun i=>(env i).den) m := by
  induction m with | nil => rfl | cons j t ih => simp [monDen,denMon,ih]

theorem row_den (env : Coords) (p : Polynomial) : common env p=denRow (fun i=>(env i).den) p := by
  induction p with | nil => rfl | cons j t ih => simp [common,denRow,ih,mon_den]

theorem restored_den (b : Book) (ps : List Pivot) (env : Coords) :
    (fun i=>(restore b ps env i).den)=denRestore ps (fun i=>(env i).den) := by
  induction ps generalizing env with
  | nil => rfl
  | cons p ps ih =>
    simp only [restore,denRestore,ih]
    congr 1;funext i;by_cases h : i=p.slot <;> simp [update,h,pivotCell,clearRow,row_den]

def fixedTime : DBlock→Nat | .one=>1 | .two=>19131876 | .three=>16

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem time_scales (g : Bool) (k : DBlock) :
    denRow (denRestore (ps g) (fun _=>1)) (timeRow k)=fixedTime k := by
  cases g <;> cases k <;> decide

theorem time_scale (b : Book) (g : Bool) (k : DBlock) :
    common (memo b (ps g) (base b)) (timeRow k)=fixedTime k := by
  rw [memo_eq,row_den,restored_den];exact time_scales g k

def negWord (b : Book) (w : Word) := times b (integer b (-1)) w

theorem neg_value (b : Book) (x : ProjectionDescent.Assignment) (w : Word) : (negWord b w).value b x= -w.value b x := by
  simp [negWord,times_value,integer_value];grobner

/-- Repeated squaring follows the integer program's binary exponentiation. -/
def power (b : Book) (w : Word) : Nat→Word
  | 0 => integer b 1
  | n+1 => let v := power b w ((n+1)/2)
           let a := times b v v
           if (n+1)%2=1 then times b a w else a
termination_by n => n

private theorem rat_power_add (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
  induction n with
  | zero => simp [Rat.pow_zero,Rat.mul_one]
  | succ n ih => simp only [Nat.add_succ,Rat.pow_succ,ih];grobner

theorem power_value (b : Book) (x : ProjectionDescent.Assignment) (w : Word) (n : Nat) :
    (power b w n).value b x=w.value b x ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [power,integer_value,Rat.pow_zero]
    | succ n =>
      have hn : (n+1)/2 < n+1 := by omega
      rw [power];split
      · rename_i odd
        rw [times_value,times_value,ih _ hn,←rat_power_add,←Rat.pow_succ]
        congr 1;omega
      · rename_i even
        rw [times_value,ih _ hn,←rat_power_add];congr 1;omega

structure Detector where
  a : Word
  q : Word
  bigQ : Word
  guard : Word

def detWords (b : Book) (k : DBlock) (pre : Coords) : Detector :=
  let e := varWord b (compactSlot k.e)
  let u := varWord b (compactSlot (k.e+1))
  let t := clearRow b pre (timeRow k)
  let s := plus b (integer b 1) (negWord b (times b (times b e t.num) u))
  let a := negWord b (power b (times b (times b (integer b (fixedTime k)) e) u) 3)
  ⟨a,times b (power b e 19) a,plus b (times b (power b e 79) a) (times b s u),times b e s⟩

structure DetCorrect (b : Book) (x : ProjectionDescent.Assignment) (k : DBlock) (d : Detector) (pre src : ProjectionDescent.Assignment) : Prop where
  a : d.a.value b x=k.a src
  q : d.q.value b x=k.q src
  bigQ : d.bigQ.value b x=k.bigQ pre src
  guard : d.guard.value b x=k.guard pre src

theorem detector_values (b : Book) (g : Bool) (y : Fin 130→Rat) (k : DBlock) :
    DetCorrect b (finiteLift y) k (detWords b k (memo b (ps g) (base b))) (preliminary g y) (seed130 y) := by
  let env := memo b (ps g) (base b)
  have al : Along b (finiteLift y) env (preliminary g y) := by
    dsimp only [env];rw [memo_eq]; exact restore_value (base_along b y) _ (good0 g)
  have num := (clear_row_value al (timeRow k)).2
  change (clearRow b env (timeRow k)).num.value b (finiteLift y)=(common env (timeRow k):Rat)*_ at num
  rw [time_value,time_scale] at num
  have d : ((fixedTime k:Nat):Rat)=k.den := by cases k <;> rfl
  constructor <;> simp only [detWords,times_value,plus_value,neg_value,power_value,variable_value,
    integer_value,Rat.intCast_natCast,Rat.intCast_one,d,DBlock.a,DBlock.q,DBlock.bigQ,DBlock.guard,DBlock.sl,seed130]
    <;> grobner

def material (b : Book) (ds : DBlock→Detector) (i : Nat) : Cell :=
  if i=136 then ⟨(ds .one).a,1⟩ else
  if i=140 then ⟨(ds .one).q,1⟩ else
  if i=141 then ⟨(ds .one).bigQ,1⟩ else
  if i=148 then ⟨(ds .two).a,1⟩ else
  if i=152 then ⟨(ds .two).q,1⟩ else
  if i=153 then ⟨(ds .two).bigQ,1⟩ else
  if i=160 then ⟨(ds .three).a,1⟩ else
  if i=164 then ⟨(ds .three).q,1⟩ else
  if i=165 then ⟨(ds .three).bigQ,1⟩ else base b i

theorem material_along (b : Book) (y : Fin 130→Rat) (z : ProjectionDescent.Assignment) (ds : DBlock→Detector)
    (h : ∀ k,DetCorrect b (finiteLift y) k (ds k) z (seed130 y)) :
    Along b (finiteLift y) (material b ds) (detectorSeed z (seed130 y)) := by
  intro i
  have cell (w : Word) (v : Rat) (eq : w.value b (finiteLift y)=v) : Represents b (finiteLift y) ⟨w,1⟩ v :=
    ⟨Nat.zero_lt_one,by change w.value b (finiteLift y)=1*v;rw [Rat.one_mul,eq]⟩
  by_cases h136 : i=136
  · subst i;exact cell _ _ (h .one).a
  by_cases h140 : i=140
  · subst i;exact cell _ _ (h .one).q
  by_cases h141 : i=141
  · subst i;exact cell _ _ (h .one).bigQ
  by_cases h148 : i=148
  · subst i;exact cell _ _ (h .two).a
  by_cases h152 : i=152
  · subst i;exact cell _ _ (h .two).q
  by_cases h153 : i=153
  · subst i;exact cell _ _ (h .two).bigQ
  by_cases h160 : i=160
  · subst i;exact cell _ _ (h .three).a
  by_cases h164 : i=164
  · subst i;exact cell _ _ (h .three).q
  by_cases h165 : i=165
  · subst i;exact cell _ _ (h .three).bigQ
  simpa only [material,detectorSeed,h136,h140,h141,h148,h152,h153,h160,h164,h165,if_false] using base_along b y i

end Physical130
