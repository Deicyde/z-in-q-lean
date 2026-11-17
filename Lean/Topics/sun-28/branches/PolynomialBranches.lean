import SunProjection
import Mathlib.Algebra.MvPolynomial.Rename

/-! The polynomial attached to a finite atlas of monic root equations, after a
common denominator has been chosen for each chart. The affine change sends
(t, c=0 or 1) to the new nonzero root z=t+c. -/
namespace Sun28.Branches
open MvPolynomial
abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℤ
def value {m : ℕ} (x : Fin m → ℚ) : Poly m →+* ℚ := eval₂Hom (Int.castRingHom ℚ) x

/-- The new coordinate is the first argument. A permutation moves it to
the first witness when the polynomial is specialized to Sun's statement. -/
noncomputable def liftP {m : ℕ} (p : Poly m) : Poly (m+1) := rename Fin.succ p

@[simp] theorem value_lift {m : ℕ} (x : Fin m → ℚ) (w : ℚ) (p : Poly m) :
    value (Fin.cases w x) (liftP p) = value x p := by
  change eval₂ (Int.castRingHom ℚ) (Fin.cases w x) (rename Fin.succ p) = _
  rw [eval₂_rename]
  rfl

@[simp] theorem value_head {m : ℕ} (x : Fin m → ℚ) (w : ℚ) :
    value (Fin.cases w x) (X 0) = w := by simp [value]

/-- Sum of squares for the equations defining a branch. -/
noncomputable def equations {m} : List (Poly m) → Poly m
  | [] => 0
  | p :: tail => p^2 + equations tail

theorem equations_spec {m} (x : Fin m → ℚ) (e : List (Poly m)) :
    value x (equations e) = 0 ↔ ∀ p ∈ e, value x p = 0 := by
  induction e with
  | nil => simp [equations]
  | cons p tail ih =>
    rw [equations, map_add, map_pow, List.forall_mem_cons]
    have ht : 0 ≤ value x (equations tail) := by
      clear ih
      induction tail with
      | nil => simp [equations]
      | cons q l h => simpa only [equations,map_add,map_pow] using add_nonneg (sq_nonneg (value x q)) h
    rw [← ih]
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (value x p)]
    · rintro ⟨h,j⟩
      simp [h,j]

/-- A monic numerator evaluated homogeneously at z=1/(D² G w), with the shift
built into each Horner step. The formula has constant value one on failed guards. -/
noncomputable def shifted {m} (D G C : Poly (m+1)) : List (Poly m) → Poly (m+1)
  | [] => 1
  | p :: tail =>
    (1-C*(D^2*G*X 0)) * shifted D G C tail +
       liftP p * D * G * X 0 * (D^2 * G * X 0)^tail.length

theorem shifted_zero {m} (x : Fin m → ℚ) (w : ℚ) (D G C : Poly m) (A : List (Poly m))
    (h : value x D = 0 ∨ value x G = 0 ∨ w = 0) :
    value (Fin.cases w x) (shifted (liftP D) (liftP G) (liftP C) A) = 1 := by
  induction A with
  | nil => simp [shifted]
  | cons a t ih =>
    simp only [shifted, map_add,map_mul,map_sub,map_one,map_pow,value_lift,value_head,ih]
    rcases h with h | h | h <;> simp [h]

theorem shifted_eval {m} (x : Fin m → ℚ) (w : ℚ) (D G C : Poly m) (A : List (Poly m))
    (hD : value x D ≠ 0) (hG : value x G ≠ 0) (hw : w ≠ 0) :
    let v := value x D ^ 2 * value x G * w
    value (Fin.cases w x) (shifted (liftP D) (liftP G) (liftP C) A) =
      v^A.length * Projection.monicValue (value x D) (v⁻¹-value x C) (A.map (value x)) := by
  dsimp only
  let v := value x D ^ 2 * value x G * w
  have hv : v ≠ 0 := by dsimp [v]; positivity
  change _ = v^A.length * Projection.monicValue (value x D) (v⁻¹-value x C) _
  induction A with
  | nil => simp [shifted,Projection.monicValue]
  | cons a t ih =>
    simp only [shifted,map_add,map_mul,map_sub,map_one,map_pow,value_lift,value_head,ih,
      List.length_cons,List.map_cons,Projection.monicValue]
    change (1-(value x C)*v) * (v^t.length * _) + value x a * value x D * value x G * w * v^t.length =
      v^(t.length+1) * (value x a / value x D + (v⁻¹ - value x C) * _)
    rw [pow_succ v]
    have ha : value x a * value x D * value x G * w = v * (value x a / value x D) := by
      dsimp [v]; field_simp
    rw [ha]
    field_simp [hv,hD]
    ring

structure Chart (m : ℕ) where
  /-- Equations cutting out the stratum. -/
  eqs : List (Poly m)
  /-- Product of the required nonzero factors. -/
  guard : Poly m
  /-- The common denominator of the non-leading coefficients. -/
  den : Poly m
  /-- Numerators, in order of ascending degree. -/
  nums : List (Poly m)

def Chart.accepts {m} (a : Chart m) (x : Fin m → ℚ) : Prop :=
  (∀ p ∈ a.eqs, value x p = 0) ∧ value x a.guard ≠ 0 ∧ value x a.den ≠ 0 ∧
    ∃ t : ℚ, Projection.monicValue (value x a.den) t (a.nums.map (value x)) = 0

noncomputable def Chart.withShift {m} (a : Chart m) (c : Poly m) : Poly (m+1) :=
  liftP (equations a.eqs) ^ 2 + (shifted (liftP a.den) (liftP a.guard) (liftP c) a.nums)^2

noncomputable def Chart.poly {m} (a : Chart m) : Poly (m+1) :=
  a.withShift 0 * a.withShift 1

theorem Chart.withShift_spec {m} (a : Chart m) (x : Fin m → ℚ) (c : Poly m) :
    (∃ w, value (Fin.cases w x) (a.withShift c) = 0) ↔
      (∀ p ∈ a.eqs, value x p = 0) ∧ value x a.guard ≠ 0 ∧ value x a.den ≠ 0 ∧
        ∃ t, t + value x c ≠ 0 ∧ Projection.monicValue (value x a.den) t (a.nums.map (value x)) = 0 := by
  constructor
  · rintro ⟨w,hw⟩
    simp only [Chart.withShift,map_add,map_pow,value_lift] at hw
    have he : value x (equations a.eqs) = 0 := by
      nlinarith [sq_nonneg (value (Fin.cases w x) (shifted (liftP a.den) (liftP a.guard) (liftP c) a.nums))]
    have hr : value (Fin.cases w x) (shifted (liftP a.den) (liftP a.guard) (liftP c) a.nums) = 0 := by
      rw [he] at hw; simpa using hw
    have good : ¬(value x a.den = 0 ∨ value x a.guard = 0 ∨ w = 0) := by
      intro bad
      rw [shifted_zero x w _ _ _ _ bad] at hr
      exact one_ne_zero hr
    push Not at good
    obtain ⟨hd,hg,hn⟩ := good
    let v := value x a.den^2 * value x a.guard * w
    have hv : v ≠ 0 := by dsimp [v]; positivity
    rw [shifted_eval x w _ _ _ _ hd hg hn] at hr
    refine ⟨(equations_spec _ _).mp he,hg,hd,v⁻¹-value x c,?_,?_⟩
    · simpa using inv_ne_zero hv
    · exact (mul_eq_zero.mp hr).resolve_left (pow_ne_zero _ hv)
  · rintro ⟨eqs,hg,hd,t,ht,hp⟩
    let w := (value x a.den^2 * value x a.guard * (t+value x c))⁻¹
    have hw : w ≠ 0 := by dsimp [w]; positivity
    refine ⟨w,?_⟩
    have he := (equations_spec x a.eqs).mpr eqs
    rw [Chart.withShift,map_add,map_pow,map_pow,value_lift,he,shifted_eval x w _ _ _ _ hd hg hw]
    have hh : (value x a.den^2 * value x a.guard * w)⁻¹ - value x c = t := by
      dsimp [w]; field_simp; abel
    rw [hh,hp]; simp

theorem Chart.poly_spec {m} (a : Chart m) (x : Fin m → ℚ) :
    (∃ w, value (Fin.cases w x) a.poly = 0) ↔ a.accepts x := by
  simp only [Chart.poly,map_mul,mul_eq_zero,exists_or,Chart.withShift_spec,map_zero,map_one,
    add_zero,Chart.accepts]
  constructor
  · rintro (⟨he,hg,hd,t,_,ht⟩ | ⟨he,hg,hd,t,_,ht⟩) <;> exact ⟨he,hg,hd,t,ht⟩
  · rintro ⟨he,hg,hd,t,ht⟩
    by_cases hz : t=0
    · right; refine ⟨he,hg,hd,t,?_,ht⟩; simp [hz]
    · exact Or.inl ⟨he,hg,hd,t,hz,ht⟩

/-- A product reuses the same witness for the finite disjunction. -/
noncomputable def atlasPolynomial {m} (charts : List (Chart m)) : Poly (m+1) :=
  (charts.map Chart.poly).prod

theorem atlas_projection {m} (charts : List (Chart m)) (x : Fin m → ℚ) :
    (∃ w, value (Fin.cases w x) (atlasPolynomial charts) = 0) ↔
      ∃ a ∈ charts, a.accepts x := by
  induction charts with
  | nil => simp [atlasPolynomial]
  | cons a as ih =>
    simp only [atlasPolynomial,List.map_cons,List.prod_cons,map_mul,mul_eq_zero,exists_or]
    rw [Chart.poly_spec]
    change _ ∨ (∃ w, value (Fin.cases w x) (atlasPolynomial as) = 0) ↔ _
    rw [ih]
    simp

end Sun28.Branches
#print axioms Sun28.Branches.equations_spec
#print axioms Sun28.Branches.shifted_zero
#print axioms Sun28.Branches.shifted_eval
#print axioms Sun28.Branches.Chart.withShift_spec
#print axioms Sun28.Branches.Chart.poly_spec
#print axioms Sun28.Branches.atlas_projection
