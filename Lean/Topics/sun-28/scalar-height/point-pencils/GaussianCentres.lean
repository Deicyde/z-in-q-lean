import ScalarEstimates
import Mathlib.NumberTheory.SumTwoSquares

/-! Every primitive norm has an integral seed of norm its squarefree part. -/
namespace Sun28.PointPencils

/-- Every divisor of a primitive norm is itself a norm, including its squarefree part. -/
theorem divisor_is_norm (a b d : ℕ) (cop : a.Coprime b) (hd : d ∣ a^2+b^2) :
    ∃ u v : ℕ, d=u^2+v^2 :=
  Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
    (ZMod.isSquare_neg_one_of_dvd hd
      (ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl cop))

theorem squarefree_seed (x : ℚ) :
    ∃ d w u v : ℕ, 0<d ∧ 0<w ∧ Squarefree d ∧
      x.num.natAbs^2+x.den^2=w^2*d ∧ d=u^2+v^2 := by
  have pos : 0<x.num.natAbs^2+x.den^2 := by have hb:=x.den_pos;positivity
  obtain ⟨d,w,hd,hw,hwq,sf⟩:=Nat.sq_mul_squarefree_of_pos pos
  obtain ⟨u,v,e⟩:=divisor_is_norm x.num.natAbs x.den d x.reduced
    (hwq ▸ dvd_mul_left d (w^2))
  exact ⟨d,w,u,v,hd,hw,sf,hwq.symm,e⟩

/-- Pythagorean gap on the auxiliary circle, retaining the factor 2. -/
theorem sum_squares_gap {p k z : ℤ} (hz : 0≤z) (hk : k≠0)
    (eq : p^2+k^2=z^2) : 2*z≤k^2+1 := by
  have kp:=sq_pos_of_ne_zero hk
  have pp : |p|^2=p^2 := sq_abs p
  have small : |p|<z := by
    by_contra! bad
    have le:=mul_self_le_mul_self hz bad
    nlinarith only [le,eq,kp,pp]
  have step : |p|≤z-1 := by omega
  have ss:=mul_self_le_mul_self (abs_nonneg p) step
  nlinarith only [ss,eq,pp]

/-- A seed with squarefree norm d recovers reduced height from its determinant. -/
theorem norm_det_bound (a b u v : ℤ) (d w : ℕ)
    (hd : 0<d) (norm : a^2+b^2=(w:ℤ)^2*d)
    (seed : (d:ℤ)=u^2+v^2) (away : u*b-v*a≠0) :
    4*(d:ℤ)*(max |a| |b|)^2≤((u*b-v*a)^2+1)^2 := by
  let k:=u*b-v*a
  let p:=u*a+v*b
  let z:ℤ:=(d:ℤ)*w
  have id : p^2+k^2=(u^2+v^2)*(a^2+b^2) := by dsimp [p,k];ring
  have eq : p^2+k^2=z^2 := by rw [id,←seed,norm];dsimp [z];ring
  have zpos : 0≤z := by dsimp [z];positivity
  have gap:=sum_squares_gap zpos away eq
  have frag:=mul_self_le_mul_self (show 0≤2*z by positivity) gap
  have coord : (max |a| |b|)^2 ≤ a^2+b^2 := by
    rcases le_total |a| |b| with h|h
    · rw [max_eq_right h,sq_abs];linarith only [sq_nonneg a]
    · rw [max_eq_left h,sq_abs];linarith only [sq_nonneg b]
  have cmp:=mul_le_mul_of_nonneg_left coord (show 0≤4*(d:ℤ) by positivity)
  rw [norm] at cmp
  dsimp only [z,k] at frag
  linarith only [cmp,(by linear_combination frag : 4*(d:ℤ)*((w:ℤ)^2*d)≤((u*b-v*a)^2+1)^2)]

/-- A fixed nonzero rational seed gives infinitely many near-tangent pairs
with both coordinates growing quadratically and the contact growing linearly. -/
theorem norm_two_family (n : ℤ) :
    let a:=n^2+2*n-1
    let b:=n^2-2*n-1
    a^2+b^2=2*(n^2+1)^2 ∧ a-b=4*n ∧
    16*(a+b+2) = 2*(a-b)^2 := by
  dsimp only
  constructor
  · ring
  constructor <;> ring

end Sun28.PointPencils
#print axioms Sun28.PointPencils.divisor_is_norm
#print axioms Sun28.PointPencils.squarefree_seed
#print axioms Sun28.PointPencils.sum_squares_gap
#print axioms Sun28.PointPencils.norm_det_bound
#print axioms Sun28.PointPencils.norm_two_family
