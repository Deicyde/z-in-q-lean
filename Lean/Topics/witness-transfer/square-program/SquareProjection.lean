import SquareData
import Gluing
namespace SquareProgram
open CircuitTransport IndependentIndices Data

def tape : Program := compile targetSeed source shape

/-- Literal source addresses in the full 21,887-instruction parent. -/
def intended (x : Assignment) : Row→Prop
  | .inherit _ n _ => valueQ source (parameter x) x n=zero
  | .replace492 => corrected x=0

def requirements (marked : Bool) (x : Assignment) := active shape marked x

theorem in_source {r : Row} (m : Bool) (x : Assignment) (h : r∈requirements m x) :
    r∈peaks++others := by
  unfold requirements active at h
  split at h
  · exact List.mem_append_left _ h
  · exact h

theorem physical_index (f : Frame) (n : Nat) (p : Bool) (mem : Row.inherit f n p∈peaks++others) :
    selected source f n p=n := by
  rw [source_spec];exact checked_index _ _ _ _ _ mem

theorem source_even (f : Frame) (n : Nat) (p : Bool) (x : Assignment) (mem : Row.inherit f n p∈peaks++others) :
    (valueQ source (parameter x) x n).im=0 := by
  have h:=selected_even source f n p x
  rwa [physical_index f n p mem] at h

theorem real_signed (f : Frame) (n : Nat) (p : Bool) (x : Assignment) (mem : Row.inherit f n p∈peaks++others) :
    let b:=Book.make targetSeed
    let coeff:=result b source.length (bank source) (table b source) (.inherit f n p)
    (coeff.num b).value b x=(valueQ source (parameter x) x n).re*scale coeff.exponent := by
  dsimp only
  rw [signed_numerator]
  dsimp only [signedValue];rw [physical_index f n p mem]

theorem replaced_signed (x : Assignment) :
    let b:=Book.make targetSeed
    let coeff:=result b source.length (bank source) (table b source) .replace492
    (coeff.num b).value b x = -(x 132)^2+(κ:Rat)*x 133*(contact (x 1))^3 := by
  exact corrected_value _ _

private theorem raw_iff (x : Assignment) (r : Row) (hr : r∈peaks++others) :
    signedValue source x r=0 ↔ intended x r := by
  cases r with
  | replace492 => rfl
  | inherit f n p =>
    dsimp only [signedValue,intended]
    rw [physical_index f n p hr]
    have odd:=source_even f n p x hr
    cases e : valueQ source (parameter x) x n with
    | mk a b =>
      rw [e] at odd
      change b=0 at odd;subst b
      change a=0 ↔ PairQ.mk a 0=PairQ.mk 0 0
      simp

theorem literal_iff (m : Bool) (x : Fin 134→Rat) :
    tape.eval m (vector x)=0 ↔ ∀ r∈requirements m (vector x),intended (vector x) r := by
  rw [tape,pointwise]
  constructor
  · intro all r hr; exact (raw_iff _ r (in_source m _ hr)).mp (all r hr)
  · intro all r hr; exact (raw_iff _ r (in_source m _ hr)).mpr (all r hr)

def frameHolds (m : Bool) (x : Fin 134→Rat) (f : Frame) : Prop :=
  ∀ r∈requirements m (vector x),r.owner=f → intended (vector x) r

theorem groups_iff (m : Bool) (x : Fin 134→Rat) :
    tape.eval m (vector x)=0 ↔ frameHolds m x .common ∧ frameHolds m x .first ∧
      frameHolds m x .second ∧ frameHolds m x .third ∧ frameHolds m x .scalar := by
  rw [literal_iff]
  constructor
  · intro h;exact ⟨fun r hr _=>h r hr,fun r hr _=>h r hr,fun r hr _=>h r hr,
                    fun r hr _=>h r hr,fun r hr _=>h r hr⟩
  · rintro ⟨c,a,b,d,s⟩ r hr
    cases hf : r.owner with
    | common => exact c r hr hf
    | first => exact a r hr hf
    | second => exact b r hr hf
    | third => exact d r hr hf
    | scalar => exact s r hr hf

theorem physical_counts :
    peaks.length=3 ∧ others.length=79 ∧
    (peaks++others).countP (fun r=>match r with | .replace492=>true | _=>false)=1 ∧
    ([Frame.common,.first,.second,.third,.scalar].map (fun f=>
      (peaks++others).countP (fun r=>decide (r.owner=f))))=[5,23,23,23,8] := by decide +kernel

theorem zero_mark :
    tape.eval true (vector (fun _ : Fin 134=>0))=0 := by
  apply (literal_iff true _).mpr
  have xx : vector (fun _ : Fin 134=>0)=fun _=>0 := by
    funext j;unfold vector;split <;> rfl
  rw [xx]
  change ∀r∈(if true=true ∧ (0:Rat)=0 then peaks else peaks++others),intended (fun _=>0) r
  rw [if_pos ⟨rfl,rfl⟩]
  intro r hr
  have prot : peaks.all (fun r=>match r with | .inherit _ _ p=>p | .replace492=>false)=true := by decide
  have bit:=List.all_eq_true.mp prot r hr
  cases r with
  | replace492 => contradiction
  | inherit f i p =>
    have hp : p=true := bit
    subst p
    change valueQ source (parameter (fun _=>0)) (fun _=>0) i=zero
    have v:=selected_axis source f i (fun _=>0) (fun _ _=>rfl)
    rwa [physical_index f i true (List.mem_append_left _ hr)] at v

theorem frame_congr (m : Bool) (f : Frame) (u v : Fin 134→Rat) (h : Agree f (vector u) (vector v)) :
    frameHolds m u f ↔ frameHolds m v f := by
  have first:=h 1 (by cases f <;> decide)
  have activeEq : requirements m (vector u)=requirements m (vector v) := by
    unfold requirements active;rw [first]
  unfold frameHolds
  rw [activeEq]
  constructor
  · intro good r hr rf
    have mem:=in_source m (vector v) hr
    have eq:=signed_local source r (vector u) (vector v) (by rw [rf];exact h)
    exact (raw_iff _ r mem).mp (eq ▸ (raw_iff _ r mem).mpr (good r hr rf))
  · intro good r hr rf
    have mem:=in_source m (vector v) hr
    have eq:=signed_local source r (vector u) (vector v) (by rw [rf];exact h)
    exact (raw_iff _ r mem).mp (eq.symm ▸ (raw_iff _ r mem).mpr (good r hr rf))

private theorem inside (f : Frame) (i : Nat) (h : inFrame f i=true) : 1≤i ∧ i≤134 := by
  cases f <;> simp [inFrame] at h <;> omega

private theorem owner_private (f : Frame) (i : Nat) (h : inFrame f i=true) (outside : 17<i) : owner i=f := by
  cases f <;> simp [inFrame] at h
  all_goals unfold owner
  all_goals repeat' split
  all_goals first | rfl | omega

theorem glue_solutions (m : Bool) (vectors : Frame→Fin 134→Rat)
    (shared : ∀f i,i.val<17 → vectors f i=vectors .common i) (rows : ∀f,frameHolds m (vectors f) f) :
    tape.eval m (vector (glue vectors))=0 := by
  have agree (f : Frame) : Agree f (vector (glue vectors)) (vector (vectors f)) := by
    intro j hj
    have bounds:=inside f j hj
    have ok : 0<j ∧ j≤134 := by omega
    simp only [vector,dif_pos ok,glue,show j-1+1=j by omega]
    by_cases common : j≤17
    · rw [show owner j=.common by simp [owner,common]]
      exact (shared f _ (by simp;omega)).symm
    · rw [owner_private f j hj (by omega)]
  have each (f) := (frame_congr m f _ _ (agree f)).mpr (rows f)
  exact (groups_iff m _).mpr ⟨each .common,each .first,each .second,each .third,each .scalar⟩
/-- Equality of the five existential conditions on each specified rational 17-tuple. -/
def onFiber (a : Fin 17→Rat) (x : Fin 134→Rat) : Prop :=
  ∀i : Fin 134, ∀hi : i.val<17, x i=a ⟨i.val,hi⟩

theorem fiber_iff (m : Bool) (a : Fin 17→Rat) :
    (∃x,onFiber a x ∧ tape.eval m (vector x)=0) ↔ ∀f,∃x,onFiber a x ∧ frameHolds m x f := by
  constructor
  · rintro ⟨x,hx,eq⟩ f
    exact ⟨x,hx,fun r hr _=>(literal_iff m x).mp eq r hr⟩
  · intro rows
    let choices (f : Frame) := Classical.choose (rows f)
    have good (f : Frame) : onFiber a (choices f) ∧ frameHolds m (choices f) f :=
      Classical.choose_spec (rows f)
    refine ⟨glue choices,?_,glue_solutions m choices ?_ (fun f=>(good f).2)⟩
    · intro i hi;exact (good (owner (i.val+1))).1 i hi
    · intro f i hi;rw [(good f).1 i hi,(good .common).1 i hi]
end SquareProgram
