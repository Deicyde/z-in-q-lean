import PairTape
import LayoutPrimitives
namespace SquareProgram
open CircuitTransport IndependentIndices

structure Tags where
  localTo : Bool
  sourceZero : Bool
  noReal : Bool
  noImag : Bool

def blankTags : Tags := ⟨true,true,true,true⟩
def tagStep (f : Frame) (o : Op) (v : Nat→Tags) : Tags :=
  match o with
  | .var i => ⟨inFrame f i,decide (i≠1),decide (i=1),decide (i≠1)⟩
  | .int c => ⟨true,decide (c=0),decide (c=0),true⟩
  | .add i j =>
    let a:=v i;let b:=v j
    ⟨a.localTo && b.localTo,a.sourceZero && b.sourceZero,a.noReal && b.noReal,a.noImag && b.noImag⟩
  | .mul i j =>
    let a:=v i;let b:=v j
    ⟨a.localTo && b.localTo,a.sourceZero || b.sourceZero,
     (a.noReal || b.noReal) && (a.noImag || b.noImag),
     (a.noReal || b.noImag) && (a.noImag || b.noReal)⟩

def AxisInput (x : Assignment) : Prop := ∀i,i≠1 → x i=0
def Agree (f : Frame) (x y : Assignment) : Prop := ∀i,inFrame f i=true → x i=y i

structure Explains (x : Assignment) (t : Tags) (a b : PairQ) : Prop where
  scope : t.localTo=true → a=b
  axis : t.sourceZero=true → AxisInput x → a=zero
  evenZero : t.noReal=true → a.re=0
  oddZero : t.noImag=true → a.im=0

private theorem vanishing_product {s t : Bool} {a b : Rat}
    (h : (s || t)=true) (l : s=true → a=0) (r : t=true → b=0) : a*b=0 := by
  rcases Bool.or_eq_true_iff.mp h with v|v
  · rw [l v,Rat.zero_mul]
  · rw [r v,Rat.mul_zero]

private theorem add_zero : addQ zero zero=zero := by
  simp [addQ,zero,Rat.zero_add]

private theorem mul_zero_left (d : Rat) (a : PairQ) : mulQ d zero a=zero := by
  simp [mulQ,zero,Rat.zero_mul,Rat.mul_zero,Rat.zero_add]

private theorem mul_zero_right (d : Rat) (a : PairQ) : mulQ d a zero=zero := by
  simp [mulQ,zero,Rat.mul_zero,Rat.zero_add]

private theorem explain_step (f : Frame) (x y : Assignment) (hxy : Agree f x y)
    (d : Rat) (o : Op) (v : Nat→Tags) (a b : Nat→PairQ) (h : ∀i,Explains x (v i) (a i) (b i)) :
    Explains x (tagStep f o v) (stepQ d x o a) (stepQ d y o b) := by
  cases o with
  | int c =>
    refine ⟨fun _=>rfl,?_,?_,fun _=>rfl⟩
    · intro z _;have q : c=0 := of_decide_eq_true z;subst c;rfl
    · intro z;have q : c=0 := of_decide_eq_true z;subst c;rfl
  | var i =>
    by_cases ind : i=1
    · subst i
      refine ⟨fun _=>rfl,?_,fun _=>rfl,?_⟩ <;> simp [tagStep]
    · refine ⟨?_,?_,?_,?_⟩
      · intro z;change varQ x i=varQ y i
        simp only [varQ,ind,if_false,hxy i z]
      · intro _ axis;change varQ x i=zero;simp [varQ,ind,axis i ind,zero]
      · simp [tagStep,ind]
      · intro _;simp [stepQ,varQ,ind]
  | add i j =>
    let hi:=h i;let hj:=h j
    refine ⟨?_,?_,?_,?_⟩
    · intro both;obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change addQ (a i) (a j)=addQ (b i) (b j)
      rw [hi.scope l,hj.scope r]
    · intro both axis;obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change addQ (a i) (a j)=zero;rw [hi.axis l axis,hj.axis r axis,add_zero]
    · intro both;obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change (a i).re+(a j).re=0;rw [hi.evenZero l,hj.evenZero r,Rat.zero_add]
    · intro both;obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change (a i).im+(a j).im=0;rw [hi.oddZero l,hj.oddZero r,Rat.zero_add]
  | mul i j =>
    let hi:=h i;let hj:=h j
    refine ⟨?_,?_,?_,?_⟩
    · intro both;obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change mulQ d (a i) (a j)=mulQ d (b i) (b j);rw [hi.scope l,hj.scope r]
    · intro either axis;change mulQ d (a i) (a j)=zero
      rcases Bool.or_eq_true_iff.mp either with l|r
      · rw [hi.axis l axis,mul_zero_left]
      · rw [hj.axis r axis,mul_zero_right]
    · intro both
      obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change (a i).re*(a j).re+d*((a i).im*(a j).im)=0
      rw [vanishing_product l hi.evenZero hj.evenZero,vanishing_product r hi.oddZero hj.oddZero,
          Rat.mul_zero,Rat.zero_add]
    · intro both
      obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp both
      change (a i).re*(a j).im+(a i).im*(a j).re=0
      rw [vanishing_product l hi.evenZero hj.oddZero,vanishing_product r hi.oddZero hj.evenZero,Rat.zero_add]

def tagAt (ops : List Op) (f : Frame) (i : Nat) : Tags :=
  getA blankTags (run (tagStep f) blankTags ops #[]) i

theorem explains (ops : List Op) (f : Frame) (d : Rat) (x y : Assignment) (agree : Agree f x y) (i : Nat) :
    Explains x (tagAt ops f i) (valueQ ops d x i) (valueQ ops d y i) := by
  apply simulate (tagStep f) (stepQ d x) (stepQ d y) blankTags zero zero (Explains x) _ _ ops i
  · exact ⟨fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl⟩
  · exact explain_step f x y agree d

end SquareProgram
