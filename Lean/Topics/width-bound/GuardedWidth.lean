import Std

/-! Eliminating a finite choice in a guarded system of rational polynomial
equations. Every branch uses the same inverse coordinate. -/

namespace GuardedWidth

inductive Expr (n : Nat) where
  | coord (i : Fin n)
  | integer (z : Int)
  | add (p q : Expr n)
  | sub (p q : Expr n)
  | mul (p q : Expr n)
deriving Inhabited

def Expr.eval {n : Nat} (x : Fin n → Rat) : Expr n → Rat
  | .coord i => x i
  | .integer z => z
  | .add p q => p.eval x + q.eval x
  | .sub p q => p.eval x - q.eval x
  | .mul p q => p.eval x * q.eval x

def squareSum {n : Nat} : List (Expr n) → Expr n
  | [] => .integer 0
  | p :: ps => .add (.mul p p) (squareSum ps)

def product {n : Nat} : List (Expr n) → Expr n
  | [] => .integer 1
  | p :: ps => .mul p (product ps)

structure Branch (n : Nat) where
  guard : Expr n
  rows : List (Expr n)

def Branch.factor {n : Nat} (b : Branch n) (inverse : Fin n) : Expr n :=
  squareSum (.sub (.mul (.coord inverse) b.guard) (.integer 1) :: b.rows)

private theorem square_nonneg (q : Rat) : 0 ≤ q*q := by
  by_cases h : 0 ≤ q
  · exact Rat.mul_nonneg h h
  · have hn : 0 ≤ -q := by grind
    have hp := Rat.mul_nonneg hn hn
    grind

private theorem squareSum_nonneg (x : Fin n → Rat) (rows : List (Expr n)) :
    0 ≤ (squareSum rows).eval x := by
  induction rows with
  | nil => exact Rat.le_refl
  | cons p ps ih => exact Rat.add_nonneg (square_nonneg (p.eval x)) ih

theorem squareSum_zero (x : Fin n → Rat) (rows : List (Expr n)) :
    (squareSum rows).eval x = 0 ↔ ∀ p ∈ rows, p.eval x = 0 := by
  induction rows with
  | nil => simp [squareSum, Expr.eval]
  | cons p ps ih =>
    have h₁ := square_nonneg (p.eval x)
    have h₂ := squareSum_nonneg x ps
    change p.eval x * p.eval x + (squareSum ps).eval x = 0 ↔ _
    constructor
    · intro h
      have h₃ : p.eval x * p.eval x = 0 := by grind
      have h₄ : (squareSum ps).eval x = 0 := by grind
      have hp := (Rat.mul_eq_zero.mp h₃).elim id id
      simpa [hp] using ih.mp h₄
    · intro h
      have hp := h p (by simp)
      have ht : ∀ q ∈ ps, q.eval x = 0 := fun q hq => h q (by simp [hq])
      simp only [hp, ih.mpr ht, Rat.zero_mul, Rat.zero_add]

theorem product_zero (x : Fin n → Rat) (ps : List (Expr n)) :
    (product ps).eval x = 0 ↔ ∃ p ∈ ps, p.eval x = 0 := by
  induction ps with
  | nil => simp [product, Expr.eval]
  | cons p ps ih => simp [product, Expr.eval, Rat.mul_eq_zero, ih]

def withInverse (v : Rat) (x : Fin n → Rat) : Fin (n+1) → Rat := Fin.cases v x

/-- Insert one new coordinate and keep all original coordinate indices distinct. -/
def lift : Expr n → Expr (n+1)
  | .coord i => .coord i.succ
  | .integer z => .integer z
  | .add p q => .add (lift p) (lift q)
  | .sub p q => .sub (lift p) (lift q)
  | .mul p q => .mul (lift p) (lift q)

theorem eval_lift (x : Fin n → Rat) (v : Rat) (p : Expr n) :
    (lift p).eval (withInverse v x) = p.eval x := by
  induction p <;> simp_all [lift, Expr.eval, withInverse]

def compile (bs : List (Branch n)) : Expr (n+1) :=
  product (bs.map fun b => (Branch.mk (lift b.guard) (b.rows.map lift)).factor 0)

/-- The free inputs are chosen before the inverse. A failed guard in one branch
has no effect on any other branch. The empty list of branches is also allowed. -/
theorem projection (bs : List (Branch n)) (x : Fin n → Rat) :
    (∃ v : Rat, (compile bs).eval (withInverse v x) = 0) ↔
      ∃ b ∈ bs, b.guard.eval x ≠ 0 ∧ ∀ p ∈ b.rows, p.eval x = 0 := by
  have spec (b : Branch n) (v : Rat) :
      ((Branch.mk (lift b.guard) (b.rows.map lift)).factor 0).eval (withInverse v x) = 0 ↔
        v * b.guard.eval x = 1 ∧ ∀ p ∈ b.rows, p.eval x = 0 := by
    rw [Branch.factor, squareSum_zero]
    simp [Expr.eval, eval_lift, withInverse]
    grind
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨f, hf, hz⟩ := (product_zero _ _).mp hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
    obtain ⟨h, rows⟩ := (spec b v).mp hz
    exact ⟨b, hb, fun e => by simp [e] at h, rows⟩
  · rintro ⟨b, hb, hn, rows⟩
    let v : Rat := 1 / b.guard.eval x
    refine ⟨v, (product_zero _ _).mpr ⟨_, List.mem_map.mpr ⟨b,hb,rfl⟩, ?_⟩⟩
    exact (spec b v).mpr ⟨Rat.div_mul_cancel hn, rows⟩

end GuardedWidth

#print axioms GuardedWidth.projection
