import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! A rational duplication map with an infinite dyadic orbit in a fixed squareclass. -/
namespace Sun28.FourContact

def cubic (a b : ℤ) (x : ℚ) : ℚ := x*(x-a)*(x-b)
def duplicate (a b : ℤ) (x : ℚ) : ℚ :=
  (x^2-(a:ℚ)*b)^2/(4*cubic a b x)
def orbit (a b : ℤ) : ℕ → ℚ
  | 0 => 1/4
  | n+1 => duplicate a b (orbit a b n)

private theorem sub_integral {x : ℚ} (c : ℤ) (hx : padicValRat 2 x < 0) :
    x-c≠0 ∧ padicValRat 2 (x-c)=padicValRat 2 x := by
  have hc : 0≤padicValRat 2 (c:ℚ) := by rw [padicValRat.of_int]; positivity
  have h : x-(c:ℚ)≠0 := by intro e; rw [sub_eq_zero.mp e] at hx; omega
  refine ⟨h,?_⟩
  by_cases z : c=0
  · simp [z]
  have xn : x≠0 := by intro z; simp [z] at hx
  have cn : -(c:ℚ)≠0 := neg_ne_zero.mpr (by exact_mod_cast z)
  rw [sub_eq_add_neg] at h ⊢
  exact padicValRat.add_eq_of_lt h xn cn (by rw [padicValRat.neg]; omega)

theorem duplicate_order (a b : ℤ) {x : ℚ} (hx : padicValRat 2 x<0) :
    padicValRat 2 (duplicate a b x)=padicValRat 2 x-2 := by
  obtain ⟨na,va⟩:=sub_integral a hx
  obtain ⟨nb,vb⟩:=sub_integral b hx
  have vx : padicValRat 2 (x^2) = 2*padicValRat 2 x := by rw [padicValRat.pow]; norm_num
  obtain ⟨nn,vn⟩:=sub_integral (a*b) (show padicValRat 2 (x^2)<0 by omega)
  push_cast at nn vn
  have xn : x≠0 := by intro z; simp [z] at hx
  have dn : cubic a b x≠0 := mul_ne_zero (mul_ne_zero xn na) nb
  have four : padicValRat 2 4=2 := by
    rw [show (4:ℚ)=2^2 by norm_num, padicValRat.pow, show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide)]
    norm_num
  unfold duplicate
  rw [padicValRat.div (pow_ne_zero _ nn) (mul_ne_zero (by norm_num) dn), padicValRat.pow,
    padicValRat.mul (by norm_num : (4:ℚ)≠0) dn, cubic,padicValRat.mul (mul_ne_zero xn na) nb,
    padicValRat.mul xn na,four,va,vb,vn,vx]
  norm_num
  ring

theorem orbit_order (a b : ℤ) (n : ℕ) :
    padicValRat 2 (orbit a b n) = -2*((n:ℤ)+1) := by
  induction n with
  | zero =>
    rw [orbit,show (1:ℚ)/4=((2:ℚ)^2)⁻¹ by norm_num]
    rw [padicValRat.inv, padicValRat.pow, show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide)]
    norm_num
  | succ n ih =>
    simp only [orbit,duplicate_order a b (show padicValRat 2 (orbit a b n)<0 by omega),ih,
      Nat.cast_succ]
    ring

theorem orbit_injective (a b : ℤ) : Function.Injective (orbit a b) := by
  intro i j e
  have h:=congrArg (padicValRat 2) e
  rw [orbit_order,orbit_order] at h
  omega

theorem orbit_avoids_integer (a b c : ℤ) (n : ℕ) : orbit a b n ≠ c := by
  intro h
  have e:=orbit_order a b n
  rw [h,padicValRat.of_int] at e
  omega

theorem cubic_ne (a b : ℤ) (n : ℕ) : cubic a b (orbit a b n) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero _ (sub_ne_zero.mpr (orbit_avoids_integer a b a n)))
    (sub_ne_zero.mpr (orbit_avoids_integer a b b n))
  simpa using orbit_avoids_integer a b 0 n

/-- The quotient of the two nonzero cubic values is a rational square. -/
theorem duplicate_square (a b : ℤ) (x : ℚ) (nonzero : cubic a b x≠0) :
    ∃ v : ℚ, cubic a b (duplicate a b x)=cubic a b x*v^2 := by
  refine ⟨(x^2-(a:ℚ)*b)*(x^2-2*(a:ℚ)*x+(a:ℚ)*b)*
    (x^2-2*(b:ℚ)*x+(a:ℚ)*b)/(8*(cubic a b x)^2),?_⟩
  let f:=cubic a b x
  have e : f=x*(x-a)*(x-b) := rfl
  have n : f≠0 := nonzero
  change (x^2-(a:ℚ)*b)^2/(4*f)*((x^2-(a:ℚ)*b)^2/(4*f)-a)*
    ((x^2-(a:ℚ)*b)^2/(4*f)-b)=f*(_/(8*f^2))^2
  field_simp [n]
  rw [e]
  ring

def seed (a b : ℤ) : ℤ := (1-4*a)*(1-4*b)

theorem orbit_square (a b : ℤ) (n : ℕ) :
    ∃ v : ℚ, cubic a b (orbit a b n)=(seed a b:ℚ)*v^2 := by
  induction n with
  | zero => refine ⟨1/8,?_⟩; simp [orbit,cubic,seed]; ring
  | succ n ih =>
    obtain ⟨v,h⟩:=ih
    obtain ⟨w,e⟩:=duplicate_square a b (orbit a b n) (cubic_ne a b n)
    exact ⟨v*w,by rw [orbit,e,h];ring⟩

end Sun28.FourContact
#print axioms Sun28.FourContact.duplicate_order
#print axioms Sun28.FourContact.orbit_order
#print axioms Sun28.FourContact.orbit_injective
#print axioms Sun28.FourContact.orbit_avoids_integer
#print axioms Sun28.FourContact.cubic_ne
#print axioms Sun28.FourContact.duplicate_square
#print axioms Sun28.FourContact.orbit_square
