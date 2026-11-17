import Std

namespace HeightSpecialization.Analytic
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

/-- The logarithm is used only on positive arguments. These three standard real-log
properties suffice, so the proof also works over ordered fields with such an operation. -/
structure LogLaw (K : Type) [Field K] [LE K] [LT K] where
  log : K→K
  monotone : ∀{x y},0<x → x≤y → log x≤log y
  power : ∀{x},0<x → ∀ n : Nat,log (x^n)=(n:K)*log x
  upper : ∀{x},0<x → log x≤x

noncomputable def bigger (x y : K) : K := by classical exact if x≤y then y else x

theorem first_le_bigger (x y : K) : x≤bigger x y := by
  classical
  unfold bigger
  split <;> grind

omit [Field K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
theorem bigger_le {x y z : K} (hx : x≤z) (hy : y≤z) : bigger x y≤z := by
  classical
  unfold bigger
  split <;> assumption

/-- Published isogeny-error expression after multiplying out its integer coefficients. -/
noncomputable def variation (l : LogLaw K) (g d : Nat) (j : K) : K :=
  ((16*g^4:Nat):K)*l.log ((7*g:Nat):K) +
  ((2*g^2:Nat):K)*l.log (d:K) +
  ((2*g^2:Nat):K)*l.log (bigger 1 (bigger (l.log (d:K)) j))

private theorem lift_le {a b : Nat} (h : a≤b) : (a:K)≤(b:K) := OrderedRing.natCast_le_natCast_of_le _ _ h

private theorem rising {X : Nat} (hx : 0<X) {a b : Nat} (h : a≤b) : X^a≤X^b :=
  Nat.pow_le_pow_right hx h

/-- All actual X are at least 65,536. At that scale monotonicity and log x ≤ x suffice. -/
theorem variation_bound (l : LogLaw K) (g d X : Nat) (gx : 12*g≤X) (dim : 0<g)
    (dpos : 0<d) (degree : d≤2304*X) (large : 65536≤X) (j : K)
    (belyi : j≤((13000000*g*X^5:Nat):K)) : variation l g d j≤((52*X^5:Nat):K) := by
  have X0 : 0<X := by omega
  have x0 : (0:K)<(X:K) := OrderedRing.pos_natCast_of_pos _ X0
  have gX : g≤X := by omega
  have dX : d≤X^2 := by
    have h:=Nat.mul_le_mul_right X (show 2304≤X by omega)
    have eq : X*X=X^2 := by grobner
    omega
  have g7 : 7*g≤X^2 := Nat.le_trans (by omega : 7*g≤X) (by simpa using rising X0 (by decide : 1≤2))
  have hj : 13000000*g*X^5≤X^8 := by
    have X2:=Nat.pow_le_pow_left large 2
    have u : 13000000≤X^2 := Nat.le_trans (by decide : 13000000≤65536^2) X2
    have h:=Nat.mul_le_mul_right (X^5) (Nat.mul_le_mul u gX)
    exact Nat.le_trans h (by apply Nat.le_of_eq;grobner)
  have logSmall (y : K) (pos : (0:K)<y) (n : Nat) (cap : y≤((X^n:Nat):K)) :
      l.log y≤((n*X:Nat):K) := by
    have up:=l.monotone pos cap
    rw [Semiring.natCast_pow,l.power x0] at up
    have scale:=OrderedRing.mul_le_mul_of_nonneg_left (l.upper x0) (OrderedRing.natCast_nonneg (a:=n) (R:=K))
    rw [Semiring.natCast_mul]
    exact Std.le_trans up scale
  have lg:=logSmall ((7*g:Nat):K) (OrderedRing.pos_natCast_of_pos _ (by omega)) 2 (lift_le g7)
  have ld:=logSmall (d:K) (OrderedRing.pos_natCast_of_pos _ dpos) 2 (lift_le dX)
  let m:=bigger (1:K) (bigger (l.log (d:K)) j)
  have mpos : (0:K)<m := Preorder.lt_of_lt_of_le OrderedRing.zero_lt_one (first_le_bigger ..)
  have ld_small:=Std.le_trans (l.upper (OrderedRing.pos_natCast_of_pos _ dpos)) (lift_le (K:=K) (Nat.le_trans dX (rising X0 (by decide : 2≤8))))
  have limit : m≤((X^8:Nat):K) := bigger_le (by simpa only [Semiring.natCast_one] using
          (lift_le (K:=K) (Nat.one_le_pow 8 X X0))) (bigger_le ld_small (Std.le_trans belyi (lift_le hj)))
  have lm:=logSmall m mpos 8 limit
  have a:=OrderedRing.mul_le_mul_of_nonneg_left lg (OrderedRing.natCast_nonneg (a:=16*g^4) (R:=K))
  have b:=OrderedRing.mul_le_mul_of_nonneg_left ld (OrderedRing.natCast_nonneg (a:=2*g^2) (R:=K))
  have c:=OrderedRing.mul_le_mul_of_nonneg_left lm (OrderedRing.natCast_nonneg (a:=2*g^2) (R:=K))
  have v:=OrderedAdd.add_le_add (OrderedAdd.add_le_add a b) c
  change variation l g d j≤_ at v
  have poly : 16*g^4*(2*X)+2*g^2*(2*X)+2*g^2*(8*X)≤52*X^5 := by
    have four:=Nat.mul_le_mul_right X (Nat.pow_le_pow_left gX 4)
    have two:=Nat.mul_le_mul_right X (Nat.pow_le_pow_left gX 2)
    have q4 : X^4*X=X^5 := by grobner
    have q2 : X^2*X=X^3 := by grobner
    rw [q4] at four
    rw [q2] at two
    have small:=Nat.le_trans two (rising X0 (by decide : 3≤5))
    change _≤52*X^5
    calc _=32*(g^4*X)+20*(g^2*X) := by grobner
         _≤32*X^5+20*X^5 := Nat.add_le_add (Nat.mul_le_mul_left 32 four) (Nat.mul_le_mul_left 20 small)
         _=_ := by grobner
  have ref:=lift_le (K:=K) poly
  simp only [Semiring.natCast_add,Semiring.natCast_mul] at ref v ⊢
  exact Std.le_trans v ref

theorem budget_integer (g X : Nat) (gx : 12*g≤X) (large : 65536≤X) :
    4*(13000000*g*X^5)+4*(52*X^5)+6*g≤4333334*X^6 := by
  have b:=Nat.mul_le_mul_right (13000000*X^5) gx
  have e1 : 12*g*(13000000*X^5)=12*(13000000*g*X^5) := by grobner
  have e2 : X*(13000000*X^5)=13000000*X^6 := by grobner
  rw [e1,e2] at b
  have s:=Nat.mul_le_mul_right (X^5) (show 624≤X by omega)
  rw [show X*X^5=X^6 by grobner] at s
  have u:=Nat.mul_le_mul_right X (show 18≤X by omega)
  rw [show X*X=X^2 by grobner] at u
  have minor:=Nat.le_trans u (rising (by omega : 0<X) (by decide : 2≤6))
  omega

/-- Multiplicity of the full isogeny factor, Bost, Belyi and the isogeny error imply
a sharper integer coefficient than 2²³, in the same height normalization. -/
theorem modular_height (l : LogLaw K) (g d gf t X : Nat) (gx : 12*g≤X) (gp : 0<g)
    (dpos : 0<d) (degree : d≤2304*X) (large : 65536≤X) (multiplicity : t≤2*gf)
    (hA J U : K) (belyi : J≤((13000000*g*X^5:Nat):K))
    (isogeny : (gf:K)*hA+2*U≤2*J+2*variation l g d J) (bost : -((3*g:Nat):K)≤2*U) :
    (t:K)*hA≤((4333334*X^6:Nat):K) := by
  by_cases pos : 0≤hA
  · have factor:=OrderedRing.mul_le_mul_of_nonneg_right (lift_le (K:=K) multiplicity) pos
    have err:=variation_bound l g d X gx gp dpos degree large J belyi
    have n:=lift_le (K:=K) (budget_integer g X gx large)
    simp only [Semiring.natCast_add,Semiring.natCast_mul] at n belyi bost factor err ⊢
    grind
  · have z:=(OrderedRing.mul_nonpos_of_nonneg_of_nonpos (OrderedRing.natCast_nonneg (a:=t) (R:=K)) (by grind : hA≤0))
    exact Std.le_trans z OrderedRing.natCast_nonneg

end HeightSpecialization.Analytic
