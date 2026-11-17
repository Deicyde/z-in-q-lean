import Cleared
namespace SquareProgram
open CircuitTransport

/-- The basis 1,z of Q[z]/(z²-d); no hypothesis on d. -/
structure PairQ where
  re : Rat
  im : Rat
  deriving Inhabited, DecidableEq

def zero : PairQ := ⟨0,0⟩
def addQ (u v : PairQ) : PairQ := ⟨u.re+v.re,u.im+v.im⟩
def mulQ (d : Rat) (u v : PairQ) : PairQ :=
  ⟨u.re*v.re+d*(u.im*v.im),u.re*v.im+u.im*v.re⟩

def varQ (x : Assignment) (i : Nat) : PairQ :=
  if i=1 then ⟨0,1⟩ else ⟨x i,0⟩

def stepQ (d : Rat) (x : Assignment) (o : Op) (v : Nat→PairQ) : PairQ :=
  match o with
  | .var i => varQ x i
  | .int c => ⟨c,0⟩
  | .add i j => addQ (v i) (v j)
  | .mul i j => mulQ d (v i) (v j)

def getA (z : α) (s : Array α) (i : Nat) := s[i]?.getD z

def run (step : Op→(Nat→α)→α) (z : α) : List Op→Array α→Array α
  | [],a => a
  | o::os,a => run step z os (a.push (step o (getA z a)))

def valueQ (ops : List Op) (d : Rat) (x : Assignment) (i : Nat) : PairQ :=
  getA zero (run (stepQ d x) zero ops #[]) i

/-- Generic forward simulation for three numerical or abstract executions. -/
theorem simulate {α β γ : Type} (f : Op→(Nat→α)→α) (g : Op→(Nat→β)→β)
    (k : Op→(Nat→γ)→γ) (a0 : α) (b0 : β) (c0 : γ) (R : α→β→γ→Prop)
    (initial : R a0 b0 c0)
    (step : ∀o l m n,(∀i,R (l i) (m i) (n i)) → R (f o l) (g o m) (k o n))
    (ops : List Op) (i : Nat) :
    R (getA a0 (run f a0 ops #[]) i) (getA b0 (run g b0 ops #[]) i)
      (getA c0 (run k c0 ops #[]) i) := by
  suffices aux : ∀ (a : Array α) (b : Array β) (c : Array γ), a.size=b.size → a.size=c.size →
      (∀j,R (getA a0 a j) (getA b0 b j) (getA c0 c j)) →
      ∀j,R (getA a0 (run f a0 ops a) j) (getA b0 (run g b0 ops b) j) (getA c0 (run k c0 ops c) j)
    from aux #[] #[] #[] rfl rfl (by intro;simpa [getA] using initial) i
  induction ops with
  | nil => intro a b c _ _ h;exact h
  | cons o os ih =>
    intro a b c ab ac agree
    apply ih _ _ _ (by simpa) (by simpa)
    intro j
    simp only [getA,Array.getElem?_push,←ab,←ac]
    by_cases eq : j=a.size
    · simp only [eq,if_true,Option.getD_some];exact step o _ _ _ agree
    · simp only [eq,if_false];exact agree j

structure PairWord where
  re : Coeff
  im : Coeff

def empty : PairWord := ⟨none,none⟩
def constant (w : Word) : Coeff := some ⟨0,w⟩

def compileStep (b : Book) (Y2 : Word) (o : Op) (v : Nat→PairWord) : PairWord :=
  match o with
  | .var i => if i=1 then ⟨none,constant (integer b 1)⟩ else ⟨constant (varWord b i),none⟩
  | .int c => ⟨constant (integer b c),none⟩
  | .add i j => ⟨addCoeff b (v i).re (v j).re,addCoeff b (v i).im (v j).im⟩
  | .mul i j =>
    ⟨addCoeff b (mulCoeff b (v i).re (v j).re) (carry b Y2 (mulCoeff b (v i).im (v j).im)),
     addCoeff b (mulCoeff b (v i).re (v j).im) (mulCoeff b (v i).im (v j).re)⟩

def decode (b : Book) (x : Assignment) (v : PairWord) : PairQ :=
  ⟨coeffVal b x v.re,coeffVal b x v.im⟩

private theorem constant_value (b : Book) (x : Assignment) (w : Word) :
    coeffVal b x (constant w)=w.value b x := by
  change w.value b x / scale 0=_
  rw [scale_zero];grobner

private theorem compiled_step (b : Book) (x : Assignment) (y : Word) (o : Op) (v : Nat→PairWord) :
    decode b x (compileStep b y o v)=stepQ (y.value b x/67830) x o (fun i=>decode b x (v i)) := by
  cases o with
  | var i =>
    by_cases h : i=1
    · rw [compileStep,if_pos h,stepQ,varQ,if_pos h]
      change PairQ.mk 0 (coeffVal b x (constant (integer b 1)))=⟨0,1⟩
      rw [constant_value,integer_value];rfl
    · rw [compileStep,if_neg h,stepQ,varQ,if_neg h]
      change PairQ.mk (coeffVal b x (constant (varWord b i))) 0=⟨x i,0⟩
      rw [constant_value,variable_value]
  | int c =>
    unfold compileStep stepQ decode
    rw [constant_value,integer_value];rfl
  | add i j =>
    unfold compileStep stepQ addQ decode
    simp only [addCoeff_value]
  | mul i j =>
    unfold compileStep stepQ mulQ decode
    simp only [addCoeff_value,mulCoeff_value,carry_value]

theorem compiled_reference (b : Book) (x : Assignment) (y : Word) (ops : List Op) (i : Nat) :
    decode b x (getA empty (run (compileStep b y) empty ops #[]) i)
      =valueQ ops (y.value b x/67830) x i := by
  apply simulate (compileStep b y) (stepQ (y.value b x/67830) x) (fun _ _=>()) empty zero ()
    (fun p q _=>decode b x p=q) rfl _ ops i
  intro o l m n h
  rw [compiled_step]
  exact congrArg _ (funext h)

end SquareProgram
