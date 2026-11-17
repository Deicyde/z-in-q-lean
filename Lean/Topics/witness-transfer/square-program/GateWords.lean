import Tags
namespace SquareProgram
open CircuitTransport IndependentIndices

def κ : Int := -80990493410131000784375977023646274345820490095244015289194989569855772668241364832628280392076492800000000000000
def Y (t : Rat) := 7*(17*(2*t+1)^2-13)
def B (t : Rat) := 2401+(Y t)^2
def contact (t : Rat) := B t*(B t-1)*(32*B t+343)
def parameter (x : Assignment) : Rat := (Y (x 1))^2/67830
def corrected (x : Assignment) : Rat := -(x 132)^2+(κ:Rat)*x 133*(contact (x 1))^3

def yword (b : Book) : Word :=
  let s:=plus b (integer b 1) (times b (integer b 2) (varWord b 1))
  times b (integer b 7) (plus b (integer b (-13)) (times b (integer b 17) (times b s s)))

def ySquareWord (b : Book) := times b (yword b) (yword b)

def contactWord (b : Book) : Word :=
  let label:=plus b (integer b 2401) (ySquareWord b)
  let u:=times b label (plus b label (integer b (-1)))
  times b u (plus b (integer b 343) (times b (integer b 32) label))

def correctedWord (b : Book) : Word :=
  let w:=varWord b 132
  let r:=contactWord b
  plus b (times b (integer b (-1)) (times b w w))
    (times b (times b (integer b κ) (varWord b 133)) (times b (times b r r) r))

theorem y_value (b : Book) (x : Assignment) : (yword b).value b x=Y (x 1) := by
  simp only [yword,Y,integer_value,plus_value,times_value,variable_value]
  grobner

theorem y2_value (b : Book) (x : Assignment) : (ySquareWord b).value b x=(Y (x 1))^2 := by
  rw [ySquareWord,times_value,y_value];grobner

theorem contact_value (b : Book) (x : Assignment) : (contactWord b).value b x=contact (x 1) := by
  simp only [contactWord,contact,B,integer_value,plus_value,times_value,y2_value]
  grobner

theorem corrected_value (b : Book) (x : Assignment) : (correctedWord b).value b x=corrected x := by
  simp only [correctedWord,corrected,integer_value,plus_value,times_value,variable_value,contact_value]
  grobner

theorem label_specializes (x : Assignment) :
    addQ ⟨2401,0⟩ (mulQ (parameter x) ⟨67830,0⟩
       (mulQ (parameter x) (varQ x 1) (varQ x 1)))=⟨B (x 1),0⟩ := by
  have clear:=Rat.div_mul_cancel (a:=(Y (x 1))^2) (by decide : (67830:Rat)≠0)
  dsimp [addQ,mulQ,varQ,parameter,B]
  congr 1 <;> grobner

inductive Row where
  | inherit (scope : Frame) (source : Nat) (protectedInput : Bool)
  | replace492
  deriving Inhabited, DecidableEq, Repr

def Row.owner : Row→Frame
  | .inherit f _ _ => f
  | .replace492 => .scalar

/-- A valid source address is local to its frame, even, and, for a peak, zero
    on the input axis. Invalid addresses read the zero immediately past the tape. -/
def selected (ops : List Op) (f : Frame) (n : Nat) (peak : Bool) : Nat :=
  let a:=tagAt ops f n
  if a.localTo && a.noImag && (!peak || a.sourceZero) then n else ops.length

private theorem run_size {α : Type} (step : Op→(Nat→α)→α) (z : α) (ops : List Op) (a : Array α) :
    (run step z ops a).size=a.size+ops.length := by
  induction ops generalizing a with
  | nil => simp [run]
  | cons o os ih => rw [run,ih];simp;omega

theorem past_source (ops : List Op) (d : Rat) (x : Assignment) :
    valueQ ops d x ops.length=zero := by
  unfold valueQ getA
  rw [Array.getElem?_eq_none (by simp [run_size])]
  rfl

theorem selected_even (ops : List Op) (f : Frame) (n : Nat) (peak : Bool) (x : Assignment) :
    (valueQ ops (parameter x) x (selected ops f n peak)).im=0 := by
  dsimp only [selected];split
  · rename_i h
    have ev:=(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
    exact (explains ops f _ x x (fun _ _=>rfl) n).oddZero ev
  · rw [past_source];rfl

theorem selected_axis (ops : List Op) (f : Frame) (n : Nat) (x : Assignment) (axis : AxisInput x) :
    valueQ ops (parameter x) x (selected ops f n true)=zero := by
  dsimp only [selected];split
  · rename_i h
    have v:=(Bool.and_eq_true_iff.mp h).2
    exact (explains ops f _ x x (fun _ _=>rfl) n).axis (by simpa using v) axis
  · exact past_source ..

theorem selected_local (ops : List Op) (f : Frame) (n : Nat) (peak : Bool) (x y : Assignment) (h : Agree f x y) :
    valueQ ops (parameter x) x (selected ops f n peak)=valueQ ops (parameter y) y (selected ops f n peak) := by
  have eq : x 1=y 1 := h 1 (by cases f <;> decide)
  have p : parameter y=parameter x := by unfold parameter;rw [eq]
  rw [p];dsimp only [selected];split
  · rename_i ok
    exact (explains ops f _ x y h n).scope (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1
  · rw [past_source,past_source]

def signedValue (ops : List Op) (x : Assignment) : Row→Rat
  | .inherit f n peak => (valueQ ops (parameter x) x (selected ops f n peak)).re
  | .replace492 => corrected x

theorem signed_local (ops : List Op) (r : Row) (x y : Assignment) (h : Agree r.owner x y) :
    signedValue ops x r=signedValue ops y r := by
  cases r with
  | inherit f n p => exact congrArg PairQ.re (selected_local ops f n p x y h)
  | replace492 =>
    have e:=h 1 (by decide);have w:=h 132 (by decide);have v:=h 133 (by decide)
    dsimp only [signedValue,corrected];rw [e,w,v]

end SquareProgram
