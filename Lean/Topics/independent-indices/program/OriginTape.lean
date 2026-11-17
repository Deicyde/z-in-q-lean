import SLP
namespace IndependentIndices
open CircuitTransport

def flag (bs : Array Bool) (i : Nat) : Bool := bs[i]?.getD false

def zeroStep (bs : Array Bool) : Op→Bool
  | .var i => decide (i≠0)
  | .int n => decide (n=0)
  | .add i j => flag bs i && flag bs j
  | .mul i j => flag bs i || flag bs j

def zeroRun : List Op→Array Bool→Array Bool
  | [],bs => bs
  | op::ops,bs => zeroRun ops (bs.push (zeroStep bs op))

private def Good (bs : Array Bool) (xs : Array Rat) :=
  bs.size=xs.size ∧ ∀ i,flag bs i=true → CircuitTransport.read xs i=0

private theorem step_good (x : Assignment) (hx : ∀i, i≠0 → x i=0) {bs : Array Bool} {xs : Array Rat} (h : Good bs xs) (op : Op) :
    zeroStep bs op=true → op.value x (CircuitTransport.read xs)=0 := by
  cases op with
  | var i => simp only [zeroStep,decide_eq_true_eq,Op.value];exact hx i
  | int n => simp only [zeroStep,decide_eq_true_eq,Op.value];rintro rfl;rfl
  | add i j =>
    simp only [zeroStep,Bool.and_eq_true,Op.value]
    rintro ⟨a,b⟩;rw [h.2 i a,h.2 j b,Rat.zero_add]
  | mul i j =>
    simp only [zeroStep,Bool.or_eq_true,Op.value]
    rintro (a|b)
    · rw [h.2 i a,Rat.zero_mul]
    · rw [h.2 j b,Rat.mul_zero]

private theorem push_good (x : Assignment) (hx : ∀i, i≠0 → x i=0) {bs : Array Bool} {xs : Array Rat} (h : Good bs xs) (op : Op) :
    Good (bs.push (zeroStep bs op)) (xs.push (op.value x (CircuitTransport.read xs))) := by
  constructor
  · simp [h.1]
  · intro i
    simp only [flag,CircuitTransport.read,Array.getElem?_push,←h.1]
    by_cases eq : i=bs.size
    · simp only [eq,if_true,Option.getD_some]
      exact step_good x hx h op
    · simp only [eq,if_false]
      exact h.2 i


private theorem run_good (x : Assignment) (hx : ∀i, i≠0 → x i=0) (ops : List Op) (bs : Array Bool) (xs : Array Rat) (h : Good bs xs) :
    Good (zeroRun ops bs) (execute x ops xs) := by
  induction ops generalizing bs xs with
  | nil => exact h
  | cons o t ih => exact ih _ _ (push_good x hx h o)

def zeroList (ops : List Op) : List Nat :=
  let bs:=zeroRun ops #[]
  (List.range bs.size).filter (flag bs)

/-- An index into the ordinary signed tape that is certified to vanish at the zero
    assignment. An out-of-range selection also reads zero. The release roundtrip
    checks the actual resolved index of each of the three marked high equations. -/
def zeroIndex (ops : List Op) (k : Nat) := (zeroList ops)[k]?.getD ops.length

theorem origin_value (ops : List Op) (k : Nat) (x : Assignment) (hx : ∀i, i≠0 → x i=0) :
    valueAt ops x (zeroIndex ops k)=0 := by
  have h:=run_good x hx ops #[] #[] (by exact ⟨rfl,fun i=>by simp [flag]⟩)
  unfold zeroIndex
  cases found : (zeroList ops)[k]? with
  | none => exact missing_zero _ _ _ (Nat.le_refl _)
  | some i =>
    have mem := List.mem_of_getElem? found
    exact h.2 i (List.mem_filter.mp mem).2
end IndependentIndices
