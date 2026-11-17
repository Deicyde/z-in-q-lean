import Words
namespace SquareProgram
open CircuitTransport

def scale (n : Nat) : Rat := ((67830:Int)^n : Int)

theorem scale_add (k l : Nat) : scale (k+l)=scale k*scale l := by
  unfold scale;rw [Int.pow_add,Rat.intCast_mul]

theorem scale_one : scale 1=67830 := rfl
theorem scale_zero : scale 0=1 := rfl

theorem scale_ne (n : Nat) : scale n≠0 := by
  induction n with
  | zero => rw [scale_zero];decide
  | succ n ih =>
    rw [scale_add,scale_one]
    intro e
    exact (Rat.mul_eq_zero.mp e).elim ih (by decide)

structure FractionWord where
  exp : Nat
  word : Word

/-- none denotes an absent component. Its degree-clearing factor is one. -/
abbrev Coeff := Option FractionWord

def Coeff.num (b : Book) : Coeff→Word
  | none => integer b 0
  | some a => a.word

def Coeff.exponent : Coeff→Nat
  | none => 0
  | some a => a.exp

def coeffVal (b : Book) (x : Assignment) : Coeff→Rat
  | none => 0
  | some a => a.word.value b x / scale a.exp

theorem numerator (b : Book) (x : Assignment) (a : Coeff) :
    (a.num b).value b x = coeffVal b x a * scale a.exponent := by
  cases a with
  | none => simp only [Coeff.num,Coeff.exponent,coeffVal,integer_value,Rat.intCast_zero,Rat.zero_mul]
  | some a => exact (Rat.div_mul_cancel (scale_ne a.exp)).symm

theorem rat_cancel {a c t : Rat} (ht : t≠0) (h : a*t=c*t) : a=c := by grind

def shifted (b : Book) (n : Nat) (f : FractionWord) : Word :=
  times b (integer b ((67830:Int)^(n-f.exp))) f.word

theorem shifted_value (b : Book) (x : Assignment) (n : Nat) (f : FractionWord) (h : f.exp≤n) :
    (shifted b n f).value b x = coeffVal b x (some f)*scale n := by
  rw [shifted,times_value,integer_value]
  have e : scale (n-f.exp)*scale f.exp=scale n := by rw [←scale_add,Nat.sub_add_cancel h]
  have v := numerator b x (some f)
  change f.word.value b x=coeffVal b x (some f)*scale f.exp at v
  change scale (n-f.exp)*f.word.value b x=_
  rw [v,←e]
  grobner

def addCoeff (b : Book) : Coeff→Coeff→Coeff
  | none,d => d
  | some c,none => some c
  | some c,some d =>
    let n:=max c.exp d.exp
    some ⟨n,plus b (shifted b n c) (shifted b n d)⟩

theorem addCoeff_value (b : Book) (x : Assignment) (a d : Coeff) :
    coeffVal b x (addCoeff b a d)=coeffVal b x a+coeffVal b x d := by
  cases a with
  | none => simp [addCoeff,coeffVal,Rat.zero_add]
  | some c =>
    cases d with
    | none => simp [addCoeff,coeffVal,Rat.add_zero]
    | some d =>
      let n:=max c.exp d.exp
      let w:=plus b (shifted b n c) (shifted b n d)
      change w.value b x/scale n=_
      apply rat_cancel (scale_ne n)
      rw [Rat.div_mul_cancel (scale_ne n)]
      dsimp only [w]
      rw [plus_value,shifted_value b x n c (Nat.le_max_left ..),
          shifted_value b x n d (Nat.le_max_right ..)]
      grobner

def mulCoeff (b : Book) : Coeff→Coeff→Coeff
  | some c,some d => some ⟨c.exp+d.exp,times b c.word d.word⟩
  | _,_ => none

theorem mulCoeff_value (b : Book) (x : Assignment) (a d : Coeff) :
    coeffVal b x (mulCoeff b a d)=coeffVal b x a*coeffVal b x d := by
  cases a with
  | none => simp [mulCoeff,coeffVal,Rat.zero_mul]
  | some c =>
    cases d with
    | none => simp [mulCoeff,coeffVal,Rat.mul_zero]
    | some d =>
      change (times b c.word d.word).value b x/scale (c.exp+d.exp)=_
      apply rat_cancel (scale_ne (c.exp+d.exp))
      rw [Rat.div_mul_cancel (scale_ne _),times_value,scale_add]
      have h := numerator b x (some c)
      have k := numerator b x (some d)
      change c.word.value b x=coeffVal b x (some c)*scale c.exp at h
      change d.word.value b x=coeffVal b x (some d)*scale d.exp at k
      rw [h,k];grobner

/-- The factor z²=Y²/67830 accompanying two odd terms. -/
def carry (b : Book) (y2 : Word) : Coeff→Coeff
  | none => none
  | some c => some ⟨c.exp+1,times b c.word y2⟩

theorem carry_value (b : Book) (x : Assignment) (y2 : Word) (a : Coeff) :
    coeffVal b x (carry b y2 a)= (y2.value b x/67830)*coeffVal b x a := by
  cases a with
  | none => simp [carry,coeffVal,Rat.mul_zero]
  | some c =>
    change (times b c.word y2).value b x/scale (c.exp+1)=_
    apply rat_cancel (scale_ne (c.exp+1))
    rw [Rat.div_mul_cancel (scale_ne _),times_value,scale_add,scale_one]
    have v := Rat.div_mul_cancel (a:=y2.value b x) (by decide : (67830:Rat)≠0)
    have h := numerator b x (some c)
    change c.word.value b x=coeffVal b x (some c)*scale c.exp at h
    rw [h];grobner

end SquareProgram
