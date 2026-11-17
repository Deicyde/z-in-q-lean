import SplitArc
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Basic

/-! Three sign ranges identify the slope with one leg-to-hypotenuse ratio of the cone. -/
namespace ZInQBlueprint.SplitRows
noncomputable section

inductive Chamber | negative | middle | upper
  deriving DecidableEq

instance : Fintype Chamber where
  elems := {.negative,.middle,.upper}
  complete x := by cases x <;> decide

def ray (x : ℚ) : Chamber := if x.num<0 then .negative else
  if x.num<(x.den:ℤ) then .middle else .upper

/-- A common scalar coordinate for the three real chambers: −x/(1−x), x, or 1/x. -/
def value : Chamber → ℝ → ℝ
  | .negative,x => x/(x-1)
  | .middle,x => x
  | .upper,x => x⁻¹

theorem value_injective {x y : ℚ} {l : Chamber} (hx : ray x=l) (hy : ray y=l)
    (eq : value l (x:ℝ)=value l (y:ℝ)) : x=y := by
  cases l with
  | negative =>
    have sign (z:ℚ) (r:ray z=.negative) : (z:ℝ)<0 := by
      have hn : z.num<0 := by
        by_contra str
        unfold ray at r
        split at r
        · contradiction
        · split at r <;> contradiction
      exact_mod_cast (Rat.num_neg.mp hn)
    have nx : (x:ℝ)-1≠0 := ne_of_lt (by linarith only [sign x hx])
    have ny : (y:ℝ)-1≠0 := ne_of_lt (by linarith only [sign y hy])
    have real := (div_eq_div_iff nx ny).mp eq
    exact_mod_cast (show (x:ℝ)=(y:ℝ) by nlinarith only [real])
  | middle => exact_mod_cast (show (x:ℝ)=(y:ℝ) from eq)
  | upper =>
    exact_mod_cast inv_injective (show (x:ℝ)⁻¹=(y:ℝ)⁻¹ from eq)

/-- The weighted positive integer rows need not be squarefree for uniqueness. -/
structure Record (x : ℚ) (B K : ℕ) where
  i : ℕ
  j : ℕ
  k : ℕ
  P : Dir
  fits : Fits i j k P
  ip : 0 < i
  jp : 0 < j
  kp : 0 < k
  ic : i≤K
  jc : j≤K
  kc : k≤K
  height : k*P.w^2≤2*B
  recover : value (ray x) (x:ℝ) = ((i*P.u^2:ℕ):ℝ)/((k*P.w^2:ℕ):ℝ)

def Record.arc {x B K} (s : Record x B K) := weighted _ _ _ _ s.fits

theorem Record.recover_arc {x B K} (s : Record x B K) :
    value (ray x) (x:ℝ) = (2*s.arc.t/(1+s.arc.t^2))^2 := by
  let a:=s.arc
  have ex : a.x^2=((s.i*s.P.u^2:ℕ):ℝ) := by
    dsimp [a,Record.arc,weighted]
    push_cast;rw [mul_pow,Real.sq_sqrt (by positivity)]
  have ez : a.z^2=((s.k*s.P.w^2:ℕ):ℝ) := by
    dsimp [a,Record.arc,weighted]
    push_cast;rw [mul_pow,Real.sq_sqrt (by positivity)]
  have rat : a.x/a.z = 2*a.t/(1+a.t^2) := by
    apply (div_eq_div_iff a.posZ.ne' (ne_of_gt (by positivity))).mpr
    obtain ⟨xx,_,zz⟩:=a.parametrization
    rw [xx,zz];ring
  rw [s.recover,←ex,←ez,←div_pow,rat]

def size (B : ℕ) := (2*B).sqrt+1

theorem Record.arc_bound {x B K} (s : Record x B K) : s.arc.z ≤ size B := by
  have ez : s.arc.z^2=((s.k*s.P.w^2:ℕ):ℝ) := by
    dsimp [Record.arc,weighted];push_cast;rw [mul_pow,Real.sq_sqrt (by positivity)]
  have h : 2*B < (size B)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
  have step := s.height.trans h.le
  have eq : s.arc.z^2≤((size B:ℕ):ℝ)^2 := by rw [ez]; exact_mod_cast step
  exact (sq_le_sq₀ s.arc.posZ.le (Nat.cast_nonneg _)).mp eq

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.value_injective
#print axioms ZInQBlueprint.SplitRows.Record.recover_arc
#print axioms ZInQBlueprint.SplitRows.Record.arc_bound
