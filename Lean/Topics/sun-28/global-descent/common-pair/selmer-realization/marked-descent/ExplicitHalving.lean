import SplitCharacters
namespace Sun28.MarkedDescent
open Sun28.SelmerRealization WeierstrassCurve WeierstrassCurve.Affine

noncomputable section
variable {l : ℕ}

set_option maxHeartbeats 550000 in
/-- For the three roots 0,l,-3l, the three square roots give a rational
half of P or of -P. Negating the latter half gives a half of P. -/
theorem half_of_squares (lp : 0<l) {x y : ℚ} (P : (twistCurve l).toAffine.Nonsingular x y)
    {a b c : ℚ} (A : x=a^2) (B : x-l=b^2) (C : x+3*l=c^2) :
    ∃ Q : RationalPoint l, 2 • Q=.some x y P := by
  have L : (0:ℚ)<l := by exact_mod_cast lp
  let X := x+a*b+a*c+b*c
  let Y := (a+b)*(a+c)*(b+c)
  have A' : X=(a+b)*(a+c) := by dsimp [X];linear_combination A
  have B' : X-l=(a+b)*(b+c) := by dsimp [X];linear_combination B
  have C' : X+3*l=(a+c)*(b+c) := by dsimp [X];linear_combination C
  have yn : Y≠0 := by
    dsimp [Y]
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h;have : a= -b := by linarith
        rw [this] at A;nlinarith
      · intro h;have : a= -c := by linarith
        rw [this] at A;nlinarith
    · intro h;have : b= -c := by linarith
      rw [this] at B;nlinarith
  have on : (twistCurve l).toAffine.Equation X Y := by
    rw [equation]
    calc
      Y^2 = ((a+b)*(a+c))*((a+b)*(b+c))*((a+c)*(b+c)) := by dsimp [Y];ring
      _ = _ := by rw [←A',←B',←C']
  have smooth : (twistCurve l).toAffine.Nonsingular X Y := by
    rw [nonsingular_iff]
    refine ⟨on,Or.inr ?_⟩
    simp [twistCurve,WeierstrassCurve.toAffine];intro H;apply yn;linarith
  have ord : Y≠(twistCurve l).toAffine.negY X Y := by rw [neg_y];intro h;apply yn;linarith
  have der : 3*X^2+4*l*X-3*(l:ℚ)^2 = (a+b+c)*(2*Y) := by
    calc
      _ = (X-l)*(X+3*l)+X*(X+3*l)+X*(X-l) := by ring
      _ = (a+b+c)*(2*Y) := by rw [B',C',A'];dsimp [Y];ring
  have tangent : (twistCurve l).toAffine.slope X X Y Y=a+b+c := by
    rw [Affine.slope_of_Y_ne rfl ord]
    simp [twistCurve,WeierstrassCurve.toAffine,Affine.negY]
    field_simp [yn]
    linear_combination der
  have doubled : (twistCurve l).toAffine.addX X X ((twistCurve l).toAffine.slope X X Y Y)=x := by
    rw [tangent]
    simp [Affine.addX,twistCurve,WeierstrassCurve.toAffine,X]
    linear_combination -A-B-C
  let H : RationalPoint l := .some X Y smooth
  have P' := nonsingular_add smooth smooth (fun eq => ord eq.right)
  have twice : 2 • H = Point.some _ _ P' := by rw [two_nsmul];exact Point.add_self_of_Y_ne ord
  have same {w z v : ℚ} (one : (twistCurve l).toAffine.Nonsingular w z)
      (two : (twistCurve l).toAffine.Nonsingular x v) (coord : w=x) :
      Point.some w z one=Point.some x v two ∨ Point.some w z one= -Point.some x v two := by
    subst w
    have hz:=equation.mp one.1
    have hw:=equation.mp two.1
    have prod : (z-v)*(z+v)=0 := by linear_combination hz-hw
    rcases mul_eq_zero.mp prod with h|h
    · left;simp only [Point.some.injEq,true_and];linarith
    · right;simp only [Point.neg_some,Point.some.injEq,true_and,neg_y];linarith
  rcases same P' P doubled with eq|eq
  · exact ⟨H,twice.trans eq⟩
  · exact ⟨-H,by
      have H' := congrArg (fun R : RationalPoint l=> -R) (twice.trans eq)
      rw [neg_neg] at H'
      rw [←H']
      abel⟩

end
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.half_of_squares
