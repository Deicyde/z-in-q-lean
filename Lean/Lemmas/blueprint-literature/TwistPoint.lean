import GenusPartition
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! The negative quadratic twist in the geometric proof of TYZ 3.5.
The affine chart is proved over Q. Points and their orders use Mathlib's
elliptic-curve group; the group-law descent is proved in the companion module TwistGroup. -/
namespace ZInQBlueprint.Rank

noncomputable section
attribute [local instance] Classical.decEq

def congruentCurve (d : ℕ) : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -(d : ℚ)^2, 0⟩

def baseCurve : WeierstrassCurve Qbar := ⟨0, 0, 0, -1, 0⟩

/-- Infinite additive order for a point of the actual elliptic group. -/
def InfiniteOrder {G : Type*} [AddCommGroup G] (P : G) : Prop :=
  ∀ k : ℕ, 0 < k → k • P ≠ 0

def PositiveRank (d : ℕ) : Prop :=
  ∃ P : (congruentCurve d).toAffine.Point, InfiniteOrder P

/-- A point in the minus part has coordinates (u,v√−d) with u,v rational.
The order here is measured on E over Qbar with Mathlib's group law. -/
def AntiPoint (d : ℕ) : Prop :=
  ∃ (u v : ℚ) (h : baseCurve.toAffine.Nonsingular (u : Qbar) ((v : Qbar) * sqrtMinus d)),
    InfiniteOrder (WeierstrassCurve.Affine.Point.some h)

/-- The Weierstrass scaling (x,y) ↦ ((√−d)²x,(√−d)³y) on affine equations. -/
theorem twistEquation_iff (d u v : ℚ) (hd : d ≠ 0) :
    -d*v^2 = u^3-u ↔ (d^2*v)^2 = (-d*u)^3-d^2*(-d*u) := by
  constructor
  · intro h
    linear_combination -d^3*h
  · intro h
    apply (mul_left_cancel₀ (pow_ne_zero 3 hd) : ∀ {a b : ℚ}, d^3*a=d^3*b → a=b)
    linear_combination -h

theorem inverseCoordinates (d x y : ℚ) (hd : d ≠ 0) :
    -d*(-x/d)=x ∧ d^2*(y/d^2)=y ∧
    -(-d*x)/d=x ∧ (d^2*y)/d^2=y := by
  constructor
  · field_simp
  constructor
  · field_simp
  constructor <;> field_simp

/-- A 2-isogeny takes twice a point of infinite order to a point of infinite order.
Only the stated exponent-two kernel property of the homomorphism is used. -/
theorem image_double_infinite {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (kerKilled : ∀ R : G, f R = 0 → (2:ℕ) • R = 0)
    (P : G) (hP : InfiniteOrder P) : InfiniteOrder (f ((2:ℕ) • P)) := by
  intro m hm h
  have hk : f (m • ((2:ℕ) • P)) = 0 := by simpa using h
  have hz := kerKilled _ hk
  have hmult : ((2*m)*2) • P = 0 := by simpa only [mul_nsmul] using hz
  exact hP _ (by positivity) hmult

/-- Geometric consequence to derive from TYZ 3.5(1), Lemma 3.18 and the
two period coefficients on journal p. 760; not asserted as a proved theorem. -/
def TYZGenusToAntiPoint : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (genusSum d : ZMod 2) = 1 → AntiPoint d

/-- The group-law descent work package, proved as negativeTwistDescent in
TwistGroup. Its conclusion includes transport of infinite order. -/
def NegativeTwistDescent : Prop :=
  ∀ d : ℕ, 0 < d → AntiPoint d → PositiveRank d

theorem positiveRank_of_row {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d)
    (comparison : DeterminantGenusComparison) (genusPoint : TYZGenusToAntiPoint)
    (descend : NegativeTwistDescent) (row : (smithM5b d).det = 1) : PositiveRank d := by
  apply descend d (by omega)
  apply genusPoint d hd hs
  rw [← comparison d hd hs, row]

end
end ZInQBlueprint.Rank

#print axioms ZInQBlueprint.Rank.twistEquation_iff
#print axioms ZInQBlueprint.Rank.inverseCoordinates
#print axioms ZInQBlueprint.Rank.image_double_infinite
#print axioms ZInQBlueprint.Rank.positiveRank_of_row
