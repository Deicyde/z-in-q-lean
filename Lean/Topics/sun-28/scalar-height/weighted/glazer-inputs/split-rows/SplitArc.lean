import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Three integral directions on a diagonal quadratic cone cannot cluster on a short arc. -/
namespace ZInQBlueprint.SplitRows
noncomputable section

/-- Homogeneous stereographic coordinates on the positive real quadrant of the unit circle. -/
structure Arc where
  x : ℝ
  y : ℝ
  z : ℝ
  posX : 0 < x
  posY : 0 < y
  posZ : 0 < z
  pythagoras : x^2+y^2=z^2

namespace Arc

def t (a : Arc) : ℝ := a.x/(a.z+a.y)
def s (a : Arc) : ℝ := (a.z+a.y)/2

theorem parametrization (a : Arc) :
    a.x=2*a.s*a.t ∧ a.y=a.s*(1-a.t^2) ∧ a.z=a.s*(1+a.t^2) := by
  have nz : a.z+a.y≠0 := ne_of_gt (add_pos a.posZ a.posY)
  unfold s t
  refine ⟨?_,?_,?_⟩
  · field_simp
  · field_simp
    nlinarith only [a.pythagoras]
  · field_simp
    nlinarith only [a.pythagoras]

theorem bounds (a : Arc) : 0<a.t ∧ a.t<1 ∧ 0<a.s ∧ a.s≤a.z := by
  have p:=a.pythagoras
  have xy : a.x≤a.z := by nlinarith only [p,sq_nonneg a.y,a.posX,a.posZ]
  have yz : a.y≤a.z := by nlinarith only [p,sq_nonneg a.x,a.posY,a.posZ]
  refine ⟨div_pos a.posX (add_pos a.posZ a.posY),(div_lt_one (add_pos a.posZ a.posY)).mpr
    (by linarith only [xy,a.posY]),?_,?_⟩
  · unfold s; linarith only [a.posY,a.posZ]
  · unfold s; linarith only [yz]

end Arc

/-- Oriented volume of three row vectors. -/
def volume {R : Type*} [CommRing R] (x y z X Y Z a b c : R) : R :=
    x*(Y*c-Z*b)-y*(X*c-Z*a)+z*(X*b-Y*a)

theorem arc_volume (a b c : Arc) :
    volume a.x a.y a.z b.x b.y b.z c.x c.y c.z =
      4*a.s*b.s*c.s*(a.t-b.t)*(a.t-c.t)*(b.t-c.t) := by
  obtain ⟨ax,ay,az⟩:=a.parametrization
  obtain ⟨bx,byv,bz⟩:=b.parametrization
  obtain ⟨cx,cy,cz⟩:=c.parametrization
  rw [ax,ay,az,bx,byv,bz,cx,cy,cz]
  unfold volume
  ring

structure Dir where
  u : ℕ
  v : ℕ
  w : ℕ

/-- A point on i u²+j v²=k w² with all three coordinates positive. -/
structure Fits (i j k : ℕ) (P : Dir) : Prop where
  x : 0 < i*P.u^2
  y : 0 < j*P.v^2
  z : i*P.u^2 + j*P.v^2 = k*P.w^2

private theorem coordinate_pos {i u : ℕ} (pos : 0 < i*u^2) :
    0 < Real.sqrt (i:ℝ)*(u:ℝ) := by
  have hi : 0 < i := Nat.pos_of_ne_zero (fun z=>by simp [z] at pos)
  have hu : 0 < u := Nat.pos_of_ne_zero (fun z=>by simp [z] at pos)
  exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hi)) (by exact_mod_cast hu)

def weighted (i j k : ℕ) (P : Dir) (h : Fits i j k P) : Arc where
  x := Real.sqrt (i:ℝ)*P.u
  y := Real.sqrt (j:ℝ)*P.v
  z := Real.sqrt (k:ℝ)*P.w
  posX := coordinate_pos h.x
  posY := coordinate_pos h.y
  posZ := coordinate_pos (h.z ▸ add_pos h.x h.y)
  pythagoras := by
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast h.z

/-! Each real volume is an integral determinant times the scale of the three columns. -/
theorem lattice_volume {i j k : ℕ} {P Q R : Dir}
    (p : Fits i j k P) (q : Fits i j k Q) (r : Fits i j k R) :
    volume (weighted _ _ _ _ p).x (weighted _ _ _ _ p).y (weighted _ _ _ _ p).z
      (weighted _ _ _ _ q).x (weighted _ _ _ _ q).y (weighted _ _ _ _ q).z
      (weighted _ _ _ _ r).x (weighted _ _ _ _ r).y (weighted _ _ _ _ r).z =
      (volume (P.u:ℤ) P.v P.w Q.u Q.v Q.w R.u R.v R.w:ℤ)*
      (Real.sqrt (i:ℝ)*Real.sqrt (j:ℝ)*Real.sqrt (k:ℝ)) := by
  simp only [weighted,volume];push_cast;ring

noncomputable def cell (H : ℕ) (a : Arc) := ⌊(3*(H:ℝ))*a.t⌋₊

theorem cell_lt {H : ℕ} (Hpos : 0<H) (a : Arc) : cell H a < 3*H := by
  apply (Nat.floor_lt (mul_nonneg (by positivity : 0≤3*(H:ℝ)) a.bounds.1.le)).mpr
  push_cast
  simpa only [mul_one] using mul_lt_mul_of_pos_left a.bounds.2.1
    (mul_pos (by norm_num : (0:ℝ)<3) (by exact_mod_cast Hpos : (0:ℝ)<H))

private theorem cell_diff {H : ℕ} {a b : Arc} (eq : cell H a=cell H b) :
    |3*(H:ℝ)*a.t-3*(H:ℝ)*b.t|≤1 := by
  have ap := Nat.floor_le (mul_nonneg (by positivity : 0≤3*(H:ℝ)) a.bounds.1.le)
  have bp := Nat.floor_le (mul_nonneg (by positivity : 0≤3*(H:ℝ)) b.bounds.1.le)
  have au := Nat.lt_floor_add_one (3*(H:ℝ)*a.t)
  have bu := Nat.lt_floor_add_one (3*(H:ℝ)*b.t)
  change (cell H a:ℝ)≤_ at ap
  change (cell H b:ℝ)≤_ at bp
  change _<(cell H a:ℝ)+1 at au
  change _<(cell H b:ℝ)+1 at bu
  rw [eq] at ap au
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem three_in_cell {i j k H : ℕ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (_hp : 0 < H)
    {P Q R : Dir} (p : Fits i j k P) (q : Fits i j k Q) (r : Fits i j k R) :
    let a := weighted _ _ _ _ p
    let b := weighted _ _ _ _ q
    let c := weighted _ _ _ _ r
    a.z≤H → b.z≤H → c.z≤H → cell H a=cell H b → cell H a=cell H c →
      a.t=b.t ∨ a.t=c.t ∨ b.t=c.t := by
  intro a b c ha hb hc same₁ same₂
  let v := volume a.x a.y a.z b.x b.y b.z c.x c.y c.z
  let D := volume (P.u:ℤ) P.v P.w Q.u Q.v Q.w R.u R.v R.w
  have av := arc_volume a b c
  change v=_ at av
  have lv := lattice_volume p q r
  change v=(D:ℝ)*(Real.sqrt (i:ℝ)*Real.sqrt (j:ℝ)*Real.sqrt (k:ℝ)) at lv
  have sh (x y : Arc) (ss : cell H x=cell H y) :
      (H:ℝ)*|x.t-y.t| ≤ 1/3 := by
    have h:=cell_diff ss
    rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 3*(H:ℝ))] at h
    linarith
  have s₁ := sh a b same₁
  have s₂ := sh a c same₂
  have s₃ := sh b c (same₁.symm.trans same₂)
  have pay (x : Arc) (bound : x.z≤H) (u v : ℝ) :
      x.s*|u-v| ≤ (H:ℝ)*|u-v| :=
    mul_le_mul_of_nonneg_right (x.bounds.2.2.2.trans bound) (abs_nonneg _)
  have factor₁ := (pay a ha a.t b.t).trans s₁
  have factor₂ := (pay b hb a.t c.t).trans s₂
  have factor₃ := (pay c hc b.t c.t).trans s₃
  have budget : |v| < 1 := calc
    _ = 4*(a.s*|a.t-b.t|)*(b.s*|a.t-c.t|)*(c.s*|b.t-c.t|) := by
      rw [av]; simp only [abs_mul,abs_of_pos a.bounds.2.2.1,
        abs_of_pos b.bounds.2.2.1,abs_of_pos c.bounds.2.2.1];norm_num;ring
    _ ≤ 4*(1/3)*(1/3)*(1/3) := by
      gcongr
      · exact mul_nonneg c.bounds.2.2.1.le (abs_nonneg _)
      · exact mul_nonneg b.bounds.2.2.1.le (abs_nonneg _)
    _ < 1 := by norm_num
  have sq_one (n : ℕ) (pos : 0 < n) : 1≤Real.sqrt (n:ℝ) := by
    apply Real.le_sqrt_of_sq_le; norm_num; exact_mod_cast pos
  by_cases dz : D=0
  · have zero : v=0 := by simp [lv,dz]
    rw [av] at zero
    rcases mul_eq_zero.mp zero with two|h
    · rcases mul_eq_zero.mp two with one|h
      · rcases mul_eq_zero.mp one with neg|h
        · exact False.elim ((mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
                a.bounds.2.2.1.ne') b.bounds.2.2.1.ne') c.bounds.2.2.1.ne') neg)
        · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · have dn : (1:ℤ)≤|D| := by have := abs_pos.mpr dz;omega
    have dr : (1:ℝ)≤|(D:ℝ)| := by exact_mod_cast dn
    have col := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (sq_one _ hi) (sq_one _ hj)) (sq_one _ hk)
    rw [lv,abs_mul,abs_of_nonneg (by positivity : 0≤Real.sqrt (i:ℝ)*Real.sqrt (j:ℝ)*Real.sqrt (k:ℝ))] at budget
    exact False.elim ((not_lt_of_ge (one_le_mul_of_one_le_of_one_le dr col)) budget)

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.Arc.parametrization
#print axioms ZInQBlueprint.SplitRows.arc_volume
#print axioms ZInQBlueprint.SplitRows.lattice_volume
#print axioms ZInQBlueprint.SplitRows.three_in_cell
