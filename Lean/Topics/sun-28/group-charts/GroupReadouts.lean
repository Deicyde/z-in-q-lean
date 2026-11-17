import GroupAtlas
import TowerRootCharts
import RationalWitness

namespace Sun28.GroupCharts
open ZInQ WeierstrassCurve WeierstrassCurve.Affine
open Sun28.Ordinates

namespace Quad
variable {R : Type*} [CommRing R]

def zero : Quad R := ofPair 0 0

@[simp] theorem zero_value (φ : R →+* ℚ) : Value φ (zero (R:=R)) 0 := by
  exact ⟨good_pair φ 0 0,by simp [zero]⟩

def totalInv (x : Quad R) : Program R (Quad R) :=
  .branch x.normNum (.pure zero) (.pure x.inv)

theorem totalInv_value (φ : R →+* ℚ) {x : Quad R} {X : K0} (h : Value φ x X) :
    Value φ (Program.eval φ (totalInv x)) X⁻¹ := by
  by_cases hz : X=0
  · subst X
    simp [totalInv,Program.eval,h.normNum.mpr rfl]
  · have nz := (not_congr h.normNum).2 hz
    have ex : eval φ x≠0 := h.value ▸ hz
    simp [totalInv,Program.eval,nz]
    exact ⟨(good_inv φ h.good).2 ex,by rw [eval_inv φ h.good ex,h.value]⟩

def totalDiv (x y : Quad R) : Program R (Quad R) :=
  Program.bind (fun z => .pure (x.mul z)) (totalInv y)

theorem totalDiv_value (φ : R →+* ℚ) {x y : Quad R} {X Y : K0}
    (hx : Value φ x X) (hy : Value φ y Y) :
    Value φ (Program.eval φ (totalDiv x y)) (X/Y) := by
  rw [totalDiv,Program.eval_bind,Program.eval,div_eq_mul_inv]
  exact hx.mul (totalInv_value φ hy)

/-- Convert the signed square-root numerators and common denominator without an auxiliary variable. -/
noncomputable def rootCode (k : Branch) (B D : R) : Quad (Polynomial R) :=
  let t := RootCharts.coordinates k B D
  ⟨t.1,t.2.1,t.2.2⟩

theorem root_value (φ : R →+* ℚ) (k : Branch) (A B D : R) (w : ℚ)
    (hg : RootCharts.guard k (φ A) (φ B) (φ D) w) :
    Value (Polynomial.eval₂RingHom φ w) (rootCode k B D) (RootCharts.reconstruct k (φ B) (φ D) w) := by
  obtain ⟨hn,e⟩ := RootCharts.coordinates_spec φ k A B D w hg
  exact ⟨hn,e.symm⟩
end Quad

namespace PointCode
variable {R : Type*} [CommRing R]

theorem represents_affineInput (φ : R →+* ℚ) (A : WitnessIndices.AffineInput) {x y : Quad R}
    (hx : Quad.Value φ x (pair A.re A.im)) (hy : Quad.Value φ y A.y) :
    Represents φ (.affine x y) A.point :=
  .affine (equation_iff_nonsingular.mp A.onCurve) hx hy

def generator : PointCode R := .affine ⟨57,-28,8⟩ ⟨-660,417,32⟩

theorem generator_correct (φ : R →+* ℚ) : Represents φ (generator (R:=R)) WitnessIndices.P := by
  rw [WitnessIndices.P,two_smul_pointR]
  apply Represents.affine
  · exact ⟨by norm_num [Quad.Good,map_ofNat],by ext <;> norm_num [Quad.eval,twoRX,map_ofNat]⟩
  · exact ⟨by norm_num [Quad.Good,map_ofNat],by ext <;> norm_num [Quad.eval,twoRY,map_ofNat]⟩

def equalTest : PointCode R → PointCode R → R
  | .infinity,.infinity => 0
  | .infinity,.affine _ _ | .affine _ _,.infinity => 1
  | .affine x y,.affine u v => (x.sub u).normNum^2+(y.sub v).normNum^2

theorem equalTest_correct (φ : R →+* ℚ) {p q : PointCode R} {P Q : curveC.toAffine.Point}
    (hp : Represents φ p P) (hq : Represents φ q Q) :
    φ (equalTest p q)=0 ↔ P=Q := by
  cases hp with
  | infinity => cases hq <;> simp [equalTest]
  | affine h hx hy =>
    cases hq with
    | infinity => simp [equalTest]
    | affine k hu hv =>
      simp only [equalTest,map_add,map_pow,sq_add_sq_eq_zero,(hx.sub hu).normNum,
        (hy.sub hv).normNum,sub_eq_zero,Point.some.injEq]

def reciprocal : PointCode R → Program R (Quad R)
  | .infinity => .pure .zero
  | .affine x _ => x.totalInv

def parameter : PointCode R → Program R (Quad R)
  | .infinity => .pure .zero
  | .affine x y => x.neg.totalDiv y

/-- This transport agrees definitionally with the one used by the frozen scalar certificate. -/
private def castCurve {b b' : K0} (eq : b=b') :
    (Scalar.curve b).Point ≃+ (Scalar.curve b').Point := by
  subst b'
  exact AddEquiv.refl _

private theorem cast_some {b b' x y : K0} (eq : b=b') (h : (Scalar.curve b).Nonsingular x y) :
    Scalar.reciprocal (castCurve eq (.some x y h))=x⁻¹ ∧
    Scalar.parameter (castCurve eq (.some x y h))= -x/y := by
  subst b'
  exact ⟨rfl,rfl⟩

theorem readouts_correct (φ : R →+* ℚ) {p : PointCode R} {P : curveC.toAffine.Point}
    (hp : Represents φ p P) :
    Quad.Value φ (Program.eval φ (reciprocal p)) (Scalar.reciprocal (WitnessIndices.scalarEquiv P)) ∧
    Quad.Value φ (Program.eval φ (parameter p)) (Scalar.parameter (WitnessIndices.scalarEquiv P)) := by
  cases hp with
  | infinity =>
    rw [map_zero]
    exact ⟨Quad.zero_value φ,Quad.zero_value φ⟩
  | @affine x y X Y h hx hy =>
    have e : -delta^2= -(3-sqrt2)^2 := by rw [delta_eq]
    change Quad.Value _ _ (Scalar.reciprocal (castCurve e (.some X Y h))) ∧
      Quad.Value _ _ (Scalar.parameter (castCurve e (.some X Y h)))
    obtain ⟨a,b⟩ := cast_some e h
    rw [a,b]
    exact ⟨Quad.totalInv_value φ hx,Quad.totalDiv_value φ hx.neg hy⟩

def parameterRatio (p q : PointCode R) : Program R (Quad R) :=
  Program.bind (fun a => Program.bind (fun b => a.totalDiv b) (parameter q)) (parameter p)

theorem parameterRatio_correct (φ : R →+* ℚ) {p q : PointCode R} {P Q : curveC.toAffine.Point}
    (hp : Represents φ p P) (hq : Represents φ q Q) :
    Quad.Value φ (Program.eval φ (parameterRatio p q))
      (Scalar.parameter (WitnessIndices.scalarEquiv P) / Scalar.parameter (WitnessIndices.scalarEquiv Q)) := by
  rw [parameterRatio,Program.eval_bind,Program.eval_bind]
  exact Quad.totalDiv_value φ (readouts_correct φ hp).2 (readouts_correct φ hq).2

end PointCode
#print axioms Quad.root_value
#print axioms PointCode.represents_affineInput
#print axioms PointCode.generator_correct
#print axioms PointCode.equalTest_correct
#print axioms PointCode.readouts_correct
#print axioms PointCode.parameterRatio_correct
end Sun28.GroupCharts
