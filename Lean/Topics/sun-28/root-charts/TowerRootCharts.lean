import IntegerRootCharts
import IteratedResultant

/-! An actual monic stage and polynomial guards over preceding integer parameters. -/
open Polynomial
namespace Sun28.RootCharts
open Ordinates ZInQBlueprint.SunResultant
noncomputable section
variable {R : Type*} [CommRing R]

/-- Equalities and inequations for the branch, in the new variable over the earlier ring. -/
def zeroTests (k : Branch) (A B : R) : List R[X] :=
  match k with
  | .mixed => []
  | .realPart | .radicalPart => [C B]
  | .zero => [C A,C B]

def nonzeroTests (k : Branch) (A B D : R) : List R[X] :=
  match k with
  | .mixed => [C D,C B,X]
  | .realPart | .radicalPart => [C D,C A]
  | .zero => [C D]

theorem guard_polynomials (φ : R →+* ℚ) (k : Branch) (A B D : R) (w : ℚ) :
    guard k (φ A) (φ B) (φ D) w ↔
      (∀ E ∈ zeroTests k A B, (E.map φ).eval w = 0) ∧
      (∀ G ∈ nonzeroTests k A B D, (G.map φ).eval w ≠ 0) := by
  cases k <;> simp [guard,zeroTests,nonzeroTests] <;> tauto

/-- The signed square-root stage over R with n earlier rational coordinates. For R = ℤ
each coefficient is an integer polynomial in those coordinates. -/
def stage {n : ℕ} (T : ParamTower R n) (k : Branch) (A B D : MvPolynomial (Fin n) R) :
    ParamTower R (n+1) :=
  T.adjoin (polynomial k A B D) (polynomial_monic k A B D)

/-- Re-express a univariate guard as a polynomial in the full enlarged tuple. -/
def asTest {n : ℕ} (E : Polynomial (MvPolynomial (Fin n) R)) : MvPolynomial (Fin (n+1)) R :=
  (MvPolynomial.finSuccEquiv R n).symm E

theorem eval_asTest (φ : R →+* ℚ) {n : ℕ} (x : Fin n → ℚ) (w : ℚ)
    (E : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.eval₂Hom φ (Fin.cons w x) (asTest E) =
      (E.map (MvPolynomial.eval₂Hom φ x)).eval w := by
  rw [ParamTower.eval_cons]; simp [asTest]

/-- After every rational specialization of the earlier coordinates the enlarged tower
with the displayed polynomial guards represents exactly the signed source equation. -/
theorem stage_square_iff (φ : R →+* ℚ) {n : ℕ} (T : ParamTower R n) (x : Fin n → ℚ)
    (A B D : MvPolynomial (Fin n) R) (y : K) :
    let ev := MvPolynomial.eval₂Hom φ x
    (ParamTower.Satisfies φ T x ∧ ev D ≠ 0 ∧ y^2 = pair (ev A / ev D) (ev B / ev D)) ↔
      ∃ (k : Branch) (w : ℚ), ParamTower.Satisfies φ (stage T k A B D) (Fin.cons w x) ∧
        (∀ E ∈ zeroTests k A B, MvPolynomial.eval₂Hom φ (Fin.cons w x) (asTest E) = 0) ∧
        (∀ G ∈ nonzeroTests k A B D, MvPolynomial.eval₂Hom φ (Fin.cons w x) (asTest G) ≠ 0) ∧
        y = reconstruct k (ev B) (ev D) w := by
  let ev := MvPolynomial.eval₂Hom φ x
  have hs (k : Branch) (w : ℚ) :
      ParamTower.Satisfies φ (stage T k A B D) (Fin.cons w x) ↔
      ParamTower.Satisfies φ T x ∧ ((polynomial k A B D).map ev).IsRoot w := by
    simp [stage,ParamTower.Satisfies,Fin.tail_cons,ev]
  dsimp only
  rw [square_iff_root ev A B D y]
  simp_rw [hs,eval_asTest]
  constructor
  · rintro ⟨hp,k,w,hg,hw,ht⟩
    obtain ⟨he,hn⟩ := (guard_polynomials ev k A B D w).mp hg
    exact ⟨k,w,⟨hp,hw⟩,he,hn,ht⟩
  · rintro ⟨k,w,⟨hp,hw⟩,he,hn,ht⟩
    exact ⟨hp,k,w,(guard_polynomials ev k A B D w).mpr ⟨he,hn⟩,hw,ht⟩

/-- A common denominator and the two numerators for the signed output. These are literal
integer polynomials after taking R to be the integer polynomial ring in the earlier variables. -/
def coordinates (k : Branch) (B D : R) : R[X] × R[X] × R[X] :=
  match k with
  | .mixed => (X^2, C (2*D*B), C (2*D)*X)
  | .realPart => (X, 0, C (2*D))
  | .radicalPart => (0, X, C (2*D))
  | .zero => (0, 0, 1)

theorem coordinates_spec (φ : R →+* ℚ) (k : Branch) (A B D : R) (w : ℚ)
    (hg : guard k (φ A) (φ B) (φ D) w) :
    let v := Polynomial.eval₂RingHom φ w
    let q := coordinates k B D
    v q.2.2 ≠ 0 ∧
      reconstruct k (φ B) (φ D) w = pair (v q.1 / v q.2.2) (v q.2.1 / v q.2.2) := by
  obtain ⟨hd,hk⟩ := hg
  cases k with
  | mixed =>
    obtain ⟨_,hw⟩ := hk
    simp [coordinates,reconstruct,pair,hd,hw,map_ofNat]
    constructor <;> field_simp
  | realPart => simp [coordinates,reconstruct,hd,map_ofNat]
  | radicalPart => simp [coordinates,reconstruct,hd,map_ofNat]
  | zero => exact ⟨by simp [coordinates],by simp [coordinates,reconstruct]; rfl⟩

/-- The two numerator polynomials on the actual affine curve y²=x³−(11−6√2)x. -/
def realNumerator (U V : R) : R := U^3+6*U*V^2-11*U+12*V
def radicalNumerator (U V : R) : R := 3*U^2*V+2*V^3-11*V+6*U

theorem curve_iff_root (φ : R →+* ℚ) (U V : R) (y : K) :
    y^2 = (pair (φ U) (φ V))^3 - pair 11 (-6)*pair (φ U) (φ V) ↔
      ∃ (k : Branch) (w : ℚ),
        guard k (ordinateReal (φ U) (φ V)) (ordinateRadical (φ U) (φ V)) 1 w ∧
        ((polynomial k (realNumerator U V) (radicalNumerator U V) (1:R)).map φ).IsRoot w ∧
        y = reconstruct k (ordinateRadical (φ U) (φ V)) 1 w := by
  rw [curve_rhs]
  simpa [ordinateReal,ordinateRadical,realNumerator,radicalNumerator,map_ofNat] using
    square_iff_root φ (realNumerator U V) (radicalNumerator U V) (1:R) y

end
end Sun28.RootCharts
#print axioms Sun28.RootCharts.guard_polynomials
#print axioms Sun28.RootCharts.eval_asTest
#print axioms Sun28.RootCharts.stage_square_iff
#print axioms Sun28.RootCharts.curve_iff_root
#print axioms Sun28.RootCharts.coordinates_spec
