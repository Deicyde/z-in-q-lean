import RationalModel
import ClusterCharts
import Mathlib.Algebra.MvPolynomial.Eval

/-! Linear changes of coordinates on the weighted models of a binary sextic.
Coordinates have weights 1, 1 and 3. A point over the base line at infinity
is included, since only the zero pair is removed. -/
noncomputable section
namespace ZInQBlueprint.CurveChart
open SexticConjugation
variable {K : Type*} [Field K]

@[ext] structure Rep (F : K × K → K) where
  base : K × K
  y : K
  nonzero : base ≠ 0
  equation : y^2 = F base

def scalings (F : K × K → K) : Setoid (Rep F) where
  r a b := ∃ c : Kˣ, b.base = c • a.base ∧ b.y = (c : K)^3*a.y
  iseqv := {
    refl a := ⟨1, by simp⟩
    symm := by
      rintro a b ⟨c,hx,hy⟩
      exact ⟨c⁻¹, by simp [hx,hy]⟩
    trans := by
      rintro a b d ⟨c,hx,hy⟩ ⟨e,kx,ky⟩
      exact ⟨e*c, by simp [kx,ky,hx,hy,mul_smul,mul_pow,mul_assoc]⟩ }

abbrev Points (F : K × K → K) := Quotient (scalings F)

private def move {F G : K × K → K} (e : (K × K) ≃ₗ[K] (K × K)) (v : Kˣ)
    (h : ∀ p, G (e p) = (v:K)^2*F p) (a : Rep F) : Rep G where
  base := e a.base
  y := v*a.y
  nonzero := fun hz => a.nonzero (e.injective (hz.trans e.map_zero.symm))
  equation := by rw [mul_pow, a.equation, h]

private def movePoints {F G : K × K → K} (e : (K × K) ≃ₗ[K] (K × K)) (v : Kˣ)
    (h : ∀ p, G (e p) = (v:K)^2*F p) : Points F → Points G :=
  Quotient.map (move e v h) (by
    rintro a b ⟨c,hx,hy⟩
    exact ⟨c, by simp [move,hx,hy,Units.smul_def,mul_left_comm]⟩)

/-- An invertible linear change on the base and a unit multiplier on Y
respect weighted scaling. Both inverse identities hold on representatives. -/
def coordinateEquiv {F G : K × K → K} (e : (K × K) ≃ₗ[K] (K × K)) (v : Kˣ)
    (h : ∀ p, G (e p) = (v:K)^2*F p) : Points F ≃ Points G := by
  have k (p : K × K) : F (e.symm p) = (↑v⁻¹:K)^2*G p := by
    have z := h (e.symm p)
    rw [e.apply_symm_apply] at z
    simp [z]
  exact {
    toFun := movePoints e v h
    invFun := movePoints e.symm v⁻¹ k
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ q =>
        apply congrArg (Quotient.mk _)
        apply Rep.ext <;> simp [move]
    right_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ q =>
        apply congrArg (Quotient.mk _)
        apply Rep.ext <;> simp [move] }

/-- Coordinates of the induced map on representatives. -/
theorem coordinateEquiv_coordinates {F G : K × K → K} (e : (K × K) ≃ₗ[K] (K × K))
    (v : Kˣ) (h : ∀ p, G (e p) = (v:K)^2*F p) (a : Rep F) :
    ∃ b : Rep G, coordinateEquiv e v h (Quotient.mk _ a) = Quotient.mk _ b ∧
      b.base = e a.base ∧ b.y = v*a.y :=
  ⟨move e v h a,rfl,rfl,rfl⟩

variable [CharZero K]

abbrev Pol := MvPolynomial (Fin 2) ℚ
def evalAt (v : K × K) : Pol →+* K :=
  MvPolynomial.eval₂Hom (Rat.castHom K) ![v.1, v.2]

private def quadEval {R : Type*} [CommRing R] (f : R →+* K) {d : K} (hd : d^2=6) :
    RationalModel.Quad R →+* K where
  toFun a := f a.re + d*f a.im
  map_zero' := by simp
  map_one' := by change f 1 + d*f 0 = 1; simp
  map_add' a b := by simp; ring
  map_mul' a b := by
    simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,map_ofNat]
    linear_combination -(f a.im)*(f b.im)*hd

omit [CharZero K] in
private theorem quadEval_omega {R : Type*} [CommRing R] (f : R →+* K) {d : K} (hd : d^2=6) :
    quadEval f hd (RationalModel.d R) = d := by simp [quadEval, RationalModel.d]

omit [CharZero K] in
private theorem quadEval_base {R : Type*} [CommRing R] (f : R →+* K) {d : K} (hd : d^2=6) (a : R) :
    quadEval f hd (algebraMap R (RationalModel.Quad R) a) = f a := by
  change f a + d*f 0 = f a
  simp

private theorem map_equation {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (d r h x z : A) :
    f (RationalModel.equation d r h x z) = RationalModel.equation (f d) (f r) (f h) (f x) (f z) := by
  simp [RationalModel.equation,binary,map_ofNat]

/-- Evaluation of the coefficient polynomial over ℚ at an arbitrary geometric point. -/
theorem rationalSextic_eval (u : ℚ) (d : K) (hd : d^2=6) (v : K × K) :
    evalAt v (RationalModel.rationalSextic u) =
    RationalModel.equation d (CoarseConic.r u : K) (CoarseConic.h u : K) v.1 v.2 := by
  have z := congrArg (quadEval (evalAt v) hd) (RationalModel.rationalSextic_eq u)
  rw [map_equation] at z
  simp only [quadEval_omega,quadEval_base,evalAt,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one] at z
  exact z

/-- This polynomial is exactly the normalization a⁻³ of the article. -/
def paperSextic (u : ℚ) : Pol := MvPolynomial.C (-1/512 : ℚ)*RationalModel.rationalSextic u

theorem scalar_normalization {d : K} (hd : d^2=6) :
    (-1/512 : K)*(2-d)^3 = ((4*(2+d))⁻¹)^3 := by
  have hn : 4*(2+d) ≠ 0 := by
    intro h
    have hp := congrArg (fun k : K => k*(2-d)) h
    have he : (8:K) = 0 := by linear_combination -hp-4*hd
    norm_num at he
  have eq : (2-d)*(4*(2+d)) = -8 := by linear_combination -4*hd
  have hi : (2-d)/(-8) = (4*(2+d))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hn).mpr
    calc
      _ = ((2-d)*(4*(2+d)))/(-8) := by ring
      _ = 1 := by rw [eq]; norm_num
  rw [← hi]
  ring

theorem paperSextic_eval (u : ℚ) (d : K) (hd : d^2=6) (v : K × K) :
    evalAt v (paperSextic u) = ((4*(2+d))⁻¹)^3*binary (d*(CoarseConic.r u : K))
      (4*(CoarseConic.h u : K)*(2+d)*(v.1+d*v.2)) (v.1-d*v.2) := by
  rw [paperSextic,map_mul,rationalSextic_eval u d hd]
  change _*((2-d)^3*_) = _
  rw [← mul_assoc, ← scalar_normalization hd]
  congr 2
  simp [evalAt]

/-- Forward coordinates are (b(x+dz), x−dz), with both inverse coordinates explicit. -/
def descentLinear (d b : K) (hd : d ≠ 0) (hb : b ≠ 0) : (K × K) ≃ₗ[K] (K × K) where
  toFun v := (b*(v.1+d*v.2),v.1-d*v.2)
  invFun v := ((v.1/b+v.2)/2,(v.1/b-v.2)/(2*d))
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' c v := by ext <;> dsimp <;> ring
  left_inv v := by ext <;> dsimp <;> field_simp [hd,hb] <;> ring
  right_inv v := by ext <;> dsimp <;> field_simp [hd,hb] <;> ring

theorem descentLinear_coordinates (d b : K) (hd : d ≠ 0) (hb : b ≠ 0) (v : K × K) :
    descentLinear d b hd hb v = (b*(v.1+d*v.2), v.1-d*v.2) ∧
      (descentLinear d b hd hb).symm v = ((v.1/b+v.2)/2, (v.1/b-v.2)/(2*d)) :=
  ⟨rfl,rfl⟩

private theorem nonzero_change {u : ℚ} (hu : u ∉ ZInQ.contactSet) (d : K) (hd : d^2=6) :
    d ≠ 0 ∧ 4*(CoarseConic.h u : K)*(2+d) ≠ 0 := by
  have hh : (CoarseConic.h u : K) ≠ 0 := by exact_mod_cast (CoarseConic.radical_units hu).2
  have hplus : 2+d ≠ 0 := by
    intro e
    have he : (2:K) = 0 := by linear_combination (d-2)*e - hd
    norm_num at he
  exact ⟨by rintro rfl; norm_num at hd, mul_ne_zero (mul_ne_zero (by norm_num) hh) hplus⟩

def model (s D : K) (v : K × K) := D*binary s v.1 v.2

/-- The arithmetic normalization over rational twisted binary forms. -/
def rational_equiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) (d : K) (hd : d^2=6) :
    Points (fun v => (δ:K)*evalAt v (RationalModel.rationalSextic u)) ≃
      Points (model (d*(CoarseConic.r u : K)) ((δ:K)*(2-d)^3)) := by
  obtain ⟨hn,hb⟩ := nonzero_change hu d hd
  apply coordinateEquiv (descentLinear d (4*(CoarseConic.h u : K)*(2+d)) hn hb) 1
  intro v
  rw [rationalSextic_eval u d hd]
  simp [model, RationalModel.equation,descentLinear,mul_assoc]

/-- The same map for the literal twist and the normalization printed in the article. -/
def paper_equiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) (d : K) (hd : d^2=6) :
    Points (fun v => (δ:K)*evalAt v (paperSextic u)) ≃
      Points (model (d*(CoarseConic.r u : K)) ((δ:K)*((4*(2+d))⁻¹)^3)) := by
  obtain ⟨hn,hb⟩ := nonzero_change hu d hd
  apply coordinateEquiv (descentLinear d (4*(CoarseConic.h u : K)*(2+d)) hn hb) 1
  intro v
  rw [paperSextic_eval u d hd]
  simp [model,descentLinear,mul_assoc]

end ZInQBlueprint.CurveChart
#print axioms ZInQBlueprint.CurveChart.coordinateEquiv
#print axioms ZInQBlueprint.CurveChart.coordinateEquiv_coordinates
#print axioms ZInQBlueprint.CurveChart.descentLinear_coordinates
#print axioms ZInQBlueprint.CurveChart.rationalSextic_eval
#print axioms ZInQBlueprint.CurveChart.scalar_normalization
#print axioms ZInQBlueprint.CurveChart.paperSextic_eval
#print axioms ZInQBlueprint.CurveChart.rational_equiv
#print axioms ZInQBlueprint.CurveChart.paper_equiv
