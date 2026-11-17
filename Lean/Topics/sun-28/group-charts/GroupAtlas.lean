import GroupLaw
import Mathlib.Data.Nat.Bits

namespace Sun28.GroupCharts
open ZInQ WeierstrassCurve WeierstrassCurve.Affine

namespace PointCode
variable {R : Type*} [CommRing R]

def neg : PointCode R → PointCode R
  | .infinity => .infinity
  | .affine x y => .affine x y.neg

theorem neg_correct (φ : R →+* ℚ) {p : PointCode R} {P : curveC.toAffine.Point}
    (hp : Represents φ p P) : Represents φ (neg p) (-P) := by
  cases hp with
  | infinity => simpa [neg] using (Represents.infinity (φ:=φ))
  | affine h hx hy =>
    rw [Point.neg_some]
    apply Represents.affine _ hx
    simpa only [curveC,shortCurve_negY] using hy.neg

/-- Double, then add the original point exactly when the next binary digit is one. -/
def step (bit : Bool) (p h : PointCode R) : Program R (PointCode R) :=
  if bit then Program.bind (fun d => addProgram d p) (addProgram h h) else addProgram h h

def bitsProgram (p : PointCode R) : List Bool → Program R (PointCode R)
  | [] => .pure .infinity
  | bit :: ns => Program.bind (step bit p) (bitsProgram p ns)

def mulProgram (n : ℕ) (p : PointCode R) := bitsProgram p n.bits

theorem mul_correct (φ : R →+* ℚ) (n : ℕ) {p : PointCode R} {P : curveC.toAffine.Point}
    (hp : Represents φ p P) :
    Represents φ (Program.eval φ (mulProgram n p)) (n • P) := by
  induction n using Nat.binaryRec' with
  | zero => simpa [mulProgram,bitsProgram,Program.eval] using (Represents.infinity (φ:=φ))
  | bit b n regular ih =>
    unfold mulProgram at ih ⊢
    rw [Nat.bits_append_bit n b regular,bitsProgram,Program.eval_bind]
    cases b with
    | false =>
      change Represents _ (Program.eval _ (addProgram _ _)) ((2*n) • P)
      simpa only [mul_nsmul,two_nsmul,nsmul_add] using add_correct φ ih ih
    | true =>
      change Represents _ (Program.eval _ (Program.bind _ _)) _
      rw [Program.eval_bind]
      change Represents _ (Program.eval _ (addProgram _ _)) ((2*n+1) • P)
      simpa only [add_nsmul,one_nsmul,mul_nsmul,two_nsmul,nsmul_add] using
        add_correct φ (add_correct φ ih ih) hp

/-- Signed scalar multiplication always uses the same affine chart for negation. -/
def signedProgram (c : ℤ) (p : PointCode R) : Program R (PointCode R) :=
  match c with
  | .ofNat n => mulProgram n p
  | .negSucc n => Program.bind (fun x => .pure (neg x)) (mulProgram (n+1) p)

theorem signed_correct (φ : R →+* ℚ) (c : ℤ) {p : PointCode R} {P : curveC.toAffine.Point}
    (hp : Represents φ p P) :
    Represents φ (Program.eval φ (signedProgram c p)) (c • P) := by
  cases c with
  | ofNat n =>
    change Represents _ (Program.eval φ (mulProgram n p)) ((n:ℤ) • P)
    rw [natCast_zsmul]
    exact mul_correct φ n hp
  | negSucc n =>
    simp only [signedProgram,Program.eval_bind,Program.eval,negSucc_zsmul]
    exact neg_correct φ (mul_correct φ (n+1) hp)

def translate (c : ℤ) (p q : PointCode R) : Program R (PointCode R) :=
  Program.bind (fun v => addProgram p (neg v)) (signedProgram c q)

theorem translate_correct (φ : R →+* ℚ) (c : ℤ) {p q : PointCode R} {P Q : curveC.toAffine.Point}
    (hp : Represents φ p P) (hq : Represents φ q Q) :
    Represents φ (Program.eval φ (translate c p q)) (P-c • Q) := by
  rw [translate,Program.eval_bind,sub_eq_add_neg]
  exact add_correct φ hp (neg_correct φ (signed_correct φ c hq))

/-- On a given input select one chart per operation; unused subtrees are never built. -/
def evalBits (φ : R →+* ℚ) (p : PointCode R) : List Bool → PointCode R
  | [] => .infinity
  | b :: bs => Program.eval φ (step b p (evalBits φ p bs))

theorem evalBits_eq (φ : R →+* ℚ) (p : PointCode R) (bs : List Bool) :
    evalBits φ p bs = Program.eval φ (bitsProgram p bs) := by
  induction bs with
  | nil => rfl
  | cons b ns ih => rw [evalBits,bitsProgram,Program.eval_bind,ih]

theorem mul_rows_correct (φ : R →+* ℚ) (n : ℕ) {p : PointCode R} {P : curveC.toAffine.Point}
    (hp : Represents φ p P) :
    ∃ q, Row.Runs φ (mulProgram n p).rows q ∧ Represents φ q (n • P) := by
  exact ⟨_,(Program.rows_correct ..).2 rfl,mul_correct φ n hp⟩

end PointCode
#print axioms PointCode.signed_correct
#print axioms PointCode.translate_correct
#print axioms PointCode.evalBits_eq
#print axioms PointCode.mul_rows_correct
end Sun28.GroupCharts
