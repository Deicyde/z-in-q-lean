import ScalarIndex

namespace StructuralReduction.Wires

inductive Op
  | var (slot : Nat)
  | int (c : Int)
  | add (a b : Nat)
  | mul (a b : Nat)

/-- Evaluate at the original absolute wire address. Backward dependencies agree with
ordinary straight-line evaluation. The default at a malformed node permits arbitrary
fallbacks outside the footprint. -/
def read (op : Nat→Op) (x : Nat→Rat) (i : Nat) : Rat :=
  match op i with
  | .var k => x k
  | .int c => (c:Rat)
  | .add a b => if _h : a<i ∧ b<i then read op x a + read op x b else 0
  | .mul a b => if _h : a<i ∧ b<i then read op x a * read op x b else 0
termination_by i

theorem read_var (op) (x) {i k} (eq : op i=.var k) : read op x i=x k := by rw [read,eq]
theorem read_int (op) (x) {i : Nat} {c : Int} (eq : op i=.int c) : read op x i=(c:Rat) := by rw [read,eq]
theorem read_add (op) (x) {i a b} (eq : op i=.add a b) (ha : a<i) (hb : b<i) :
    read op x i=read op x a+read op x b := by rw [read,eq];simp only [dif_pos (And.intro ha hb)]
theorem read_mul (op) (x) {i a b} (eq : op i=.mul a b) (ha : a<i) (hb : b<i) :
    read op x i=read op x a*read op x b := by rw [read,eq];simp only [dif_pos (And.intro ha hb)]

def residual (b t s j : Rat) := j^2*(t^2-17*b)*(t^2+3*(17*b))-
  (289-17*b)*(17*b-s^2)*(17*b+3*s^2)

def gateY (t : Rat) := 7*(17*(2*t+1)^2-13)
def rOfY2 (e : Rat) := let B:=2401+e; B*(B-1)*(32*B+343)
def contact (t : Rat) := rOfY2 ((gateY t)^2)
def normInput (x : Nat→Rat) := (x 126)^2-2*(x 127)^2

theorem expanded_contact (e : Rat) : (67830:Rat)^3*rOfY2 e=
    444713220000*67830^3+37639814924250*(67830^2)*e+
    1061921980482300*67830*e^2+9986548821984000*e^3 := by unfold rOfY2;grobner

end StructuralReduction.Wires
