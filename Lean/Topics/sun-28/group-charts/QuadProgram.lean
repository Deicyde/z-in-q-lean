import ZInQKernel.Model.Field.CurveC

/-! Rationally parametrized coordinates a+b√2 with a common denominator in R. -/
namespace Sun28.GroupCharts
open ZInQ
universe u
structure Quad (R : Type u) where
  re : R
  im : R
  den : R

namespace Quad
variable {R : Type*} [CommRing R]

def ofPair (a b : R) : Quad R := ⟨a,b,1⟩
def neg (x : Quad R) : Quad R := ⟨-x.re,-x.im,x.den⟩
def conj (x : Quad R) : Quad R := ⟨x.re,-x.im,x.den⟩
def add (x y : Quad R) : Quad R :=
  ⟨x.re*y.den+y.re*x.den,x.im*y.den+y.im*x.den,x.den*y.den⟩
def sub (x y : Quad R) : Quad R := add x (neg y)
def mul (x y : Quad R) : Quad R :=
  ⟨x.re*y.re+2*x.im*y.im,x.re*y.im+x.im*y.re,x.den*y.den⟩
def normNum (x : Quad R) : R := x.re^2-2*x.im^2
def inv (x : Quad R) : Quad R := ⟨x.re*x.den,-x.im*x.den,normNum x⟩
def div (x y : Quad R) : Quad R := mul x (inv y)

/-- The specialized common denominator is nonzero. Each inverse separately checks its operand. -/
def Good (φ : R →+* ℚ) (x : Quad R) : Prop := φ x.den≠0
def eval (φ : R →+* ℚ) (x : Quad R) : K0 := ⟨φ x.re / φ x.den,φ x.im / φ x.den⟩

variable (φ : R →+* ℚ)

@[simp] theorem map_two : φ (2:R)=2 := by simpa only [one_add_one_eq_two] using φ.map_add 1 1 |>.trans (by rw [map_one]; norm_num)

@[simp] theorem good_pair (a b : R) : Good φ (ofPair a b) := by simp [Good,ofPair]
@[simp] theorem eval_pair (a b : R) : eval φ (ofPair a b) = ⟨φ a,φ b⟩ := by simp [eval,ofPair]

@[simp] theorem good_neg (x : Quad R) : Good φ (neg x) ↔ Good φ x := Iff.rfl
@[simp] theorem eval_neg (x : Quad R) : eval φ (neg x) = -eval φ x := by
  ext <;> simp [eval,neg,neg_div]

@[simp] theorem good_conj (x : Quad R) : Good φ (conj x) ↔ Good φ x := Iff.rfl
@[simp] theorem eval_conj (x : Quad R) : eval φ (conj x)=star (eval φ x) := by
  rw [K0.star_eq']; ext <;> simp [eval,conj,neg_div]

@[simp] theorem good_add (x y : Quad R) : Good φ (add x y) ↔ Good φ x ∧ Good φ y := by
  simp [Good,add]
theorem eval_add {x y : Quad R} (hx : Good φ x) (hy : Good φ y) :
    eval φ (add x y) = eval φ x + eval φ y := by
  unfold Good at hx hy
  ext <;> simp [eval,add] <;> field_simp [hx,hy]

@[simp] theorem good_sub (x y : Quad R) : Good φ (sub x y) ↔ Good φ x ∧ Good φ y := by
  simp [sub]
theorem eval_sub {x y : Quad R} (hx : Good φ x) (hy : Good φ y) :
    eval φ (sub x y) = eval φ x - eval φ y := by rw [sub,eval_add φ hx ((good_neg φ y).2 hy),eval_neg,sub_eq_add_neg]

@[simp] theorem good_mul (x y : Quad R) : Good φ (mul x y) ↔ Good φ x ∧ Good φ y := by
  simp [Good,mul]
theorem eval_mul {x y : Quad R} (hx : Good φ x) (hy : Good φ y) :
    eval φ (mul x y) = eval φ x * eval φ y := by
  unfold Good at hx hy
  ext <;> simp [eval,mul] <;> field_simp [hx,hy]

theorem normNum_zero_iff {x : Quad R} (hx : Good φ x) :
    φ (normNum x)=0 ↔ eval φ x=0 := by
  have e : φ (normNum x)=(φ x.den)^2*QuadraticAlgebra.norm (eval φ x) := by
    rw [K0.norm_eq]
    unfold Good at hx
    simp [normNum,eval]
    field_simp [hx]
  rw [e,mul_eq_zero,K0.norm_eq_zero_iff]
  exact or_iff_right (pow_ne_zero 2 hx)

@[simp] theorem good_inv {x : Quad R} (hx : Good φ x) : Good φ (inv x) ↔ eval φ x≠0 := by
  change φ (normNum x)≠0 ↔ _
  exact not_congr (normNum_zero_iff φ hx)

theorem eval_inv {x : Quad R} (hx : Good φ x) (hn : eval φ x≠0) :
    eval φ (inv x)=(eval φ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have norm : φ x.re^2-2*φ x.im^2 ≠ 0 := by
    simpa [normNum] using (not_congr (normNum_zero_iff φ hx)).2 hn
  unfold Good at hx
  ext <;> simp [eval,inv,normNum] <;> field_simp [norm,hx] <;> ring

@[simp] theorem good_div {x y : Quad R} (hy : Good φ y) :
    Good φ (div x y) ↔ Good φ x ∧ eval φ y≠0 := by
  rw [div,good_mul,good_inv φ hy]
theorem eval_div {x y : Quad R} (hx : Good φ x) (hy : Good φ y) (hn : eval φ y≠0) :
    eval φ (div x y) = eval φ x / eval φ y := by
  rw [div,eval_mul φ hx ((good_inv φ hy).2 hn),eval_inv φ hy hn,div_eq_mul_inv]

end Quad

/-- A finite list of polynomial equations and inequations attached to a symbolic result. -/
structure Row (R α : Type*) where
  equations : List R
  guards : List R
  output : α

namespace Row
variable {R α β : Type*}
def pure (a : α) : Row R α := ⟨[],[],a⟩
def join (x : Row R α) (y : Row R β) : Row R β :=
  ⟨x.equations++y.equations,x.guards++y.guards,y.output⟩
def Live [CommRing R] (φ : R →+* ℚ) (x : Row R α) : Prop :=
  (∀ e ∈ x.equations,φ e=0) ∧ ∀ g ∈ x.guards,φ g≠0
@[simp] theorem live_pure [CommRing R] (φ : R →+* ℚ) (a : α) : (pure (R:=R) a).Live φ := by simp [Live,pure]
@[simp] theorem live_join [CommRing R] (φ : R →+* ℚ) (x : Row R α) (y : Row R β) :
    (join x y).Live φ ↔ x.Live φ ∧ y.Live φ := by
  simp only [Live,join,List.mem_append]; aesop

def bind (xs : List (Row R α)) (f : α → List (Row R β)) : List (Row R β) :=
  xs.flatMap fun x => (f x.output).map (join x)

def Runs [CommRing R] (φ : R →+* ℚ) (xs : List (Row R α)) (a : α) : Prop :=
  ∃ r ∈ xs, r.Live φ ∧ r.output=a

theorem runs_bind [CommRing R] (φ : R →+* ℚ) (xs : List (Row R α)) (f : α → List (Row R β)) (y : β) :
    Runs φ (bind xs f) y ↔ ∃ x, Runs φ xs x ∧ Runs φ (f x) y := by
  constructor
  · rintro ⟨r,hr,live,out⟩
    obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    obtain ⟨a,b⟩ := (live_join ..).1 live
    exact ⟨s.output,⟨s,hs,a,rfl⟩,t,ht,b,out⟩
  · rintro ⟨x,⟨s,hs,slive,rfl⟩,t,ht,tlive,out⟩
    exact ⟨s.join t,List.mem_flatMap.mpr ⟨s,hs,List.mem_map.mpr ⟨t,ht,rfl⟩⟩,
      (live_join ..).2 ⟨slive,tlive⟩,out⟩
end Row

#print axioms Quad.eval_add
#print axioms Quad.eval_mul
#print axioms Quad.normNum_zero_iff
#print axioms Quad.eval_div
#print axioms Row.runs_bind
end Sun28.GroupCharts

