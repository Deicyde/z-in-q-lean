import CurveChart

/-! The regular and pole charts on weighted homogeneous points. -/
noncomputable section
namespace ZInQBlueprint.CurveChart
open SexticConjugation
variable {R : Type*} [CommRing R]

def regularBinary (s h x z : R) : R :=
  (-4+3*s)*x^6 - 192*h*x^5*z - 96*(28+9*s)*x^4*z^2 - 4096*h*x^3*z^3 +
    3072*(28-9*s)*x^2*z^4 - 196608*h*x*z^5 + 32768*(4+3*s)*z^6

theorem regular_identity {s h : R} (ht : 9*s^2-32 = -32*h^2) (x z : R) :
    binary s (h*x) z = h^6*regularBinary s h x z := by
  simp only [binary,regularBinary,ht]
  ring

def poleBinary (w x z : R) : R :=
  let t := 9-32*w^2
  729*(3-4*w)*x^6 + 1458*t*x^5*z + 243*t*(28*w+9)*x^4*z^2 - 108*t^2*x^3*z^3 +
    27*t^2*(28*w-9)*x^2*z^4 + 18*t^3*x*z^5 - t^3*(4*w+3)*z^6

theorem pole_affine (w x : R) : poleBinary w x 1 = ClusterCharts.pole x w := by
  simp [poleBinary,ClusterCharts.pole]

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem pole_identity (w x z : K) (hw : w ≠ 0) :
    poleBinary w x z = w^7*binary w⁻¹ (3*w⁻¹*x) z := by
  simp only [poleBinary,binary]
  field_simp [hw]
  ring

def diagonal (a : K) (ha : a ≠ 0) : (K × K) ≃ₗ[K] (K × K) where
  toFun v := (a*v.1, v.2)
  invFun v := (v.1/a, v.2)
  map_add' v w := by
    refine Prod.ext ?_ ?_
    · exact mul_add _ _ _
    · rfl
  map_smul' c v := by
    refine Prod.ext ?_ ?_
    · exact mul_left_comm _ _ _
    · rfl
  left_inv v := by
    refine Prod.ext ?_ ?_
    · change a*v.1/a = v.1
      field_simp
    · rfl
  right_inv v := by
    refine Prod.ext ?_ ?_
    · change a*(v.1/a) = v.1
      field_simp
    · rfl

omit [CharZero K] in
def regular_equiv (s h D : K) (hh : h ≠ 0) (ht : 9*s^2-32 = -32*h^2) :
    Points (fun v => D*regularBinary s h v.1 v.2) ≃ Points (model s D) := by
  apply coordinateEquiv (diagonal h hh) (Units.mk0 (h^3) (pow_ne_zero _ hh))
  intro v
  change D*binary s (h*v.1) v.2 = (h^3)^2*(D*regularBinary s h v.1 v.2)
  rw [regular_identity ht]
  ring

def pole_equiv (w D : K) (hw : w ≠ 0) :
    Points (fun v => (D/w)*(poleBinary w v.1 v.2/729)) ≃ Points (model w⁻¹ D) := by
  have h3 : 3*w⁻¹ ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hw)
  apply coordinateEquiv (diagonal (3*w⁻¹) h3) (Units.mk0 ((3*w⁻¹)^3) (pow_ne_zero _ h3))
  intro v
  change D*binary w⁻¹ ((3*w⁻¹)*v.1) v.2 =
    ((3*w⁻¹)^3)^2*((D/w)*(poleBinary w v.1 v.2/729))
  rw [pole_identity w _ _ hw]
  field_simp [hw]
  ring

/-- Composition with the literal rational polynomial on the regular chart. -/
def paper_regular_equiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) (d : K) (hd : d^2=6) :
    let s := d*(CoarseConic.r u : K)
    let h := (CoarseConic.h u : K)
    let D := (δ:K)*((4*(2+d))⁻¹)^3
    Points (fun v => (δ:K)*evalAt v (paperSextic u)) ≃ Points (fun v => D*regularBinary s h v.1 v.2) := by
  have hh : (CoarseConic.h u : K) ≠ 0 := by exact_mod_cast (CoarseConic.radical_units hu).2
  exact (paper_equiv hu δ d hd).trans
    (regular_equiv _ _ _ hh (CoarseConic.sextic_parameters u hd).2).symm

/-- Here w = (√6 r(u))⁻¹ for the rational u and the equation retains λδ/w. -/
def paper_pole_equiv {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) (d : K) (hd : d^2=6) :
    let w := (d*(CoarseConic.r u : K))⁻¹
    let D := (δ:K)*((4*(2+d))⁻¹)^3
    Points (fun v => (δ:K)*evalAt v (paperSextic u)) ≃ Points (fun v => (D/w)*(poleBinary w v.1 v.2/729)) := by
  have hr : (CoarseConic.r u : K) ≠ 0 := by exact_mod_cast (CoarseConic.radical_units hu).1
  have hn : d ≠ 0 := by rintro rfl; norm_num at hd
  have e := (pole_equiv (d*(CoarseConic.r u : K))⁻¹ ((δ:K)*((4*(2+d))⁻¹)^3)
    (inv_ne_zero (mul_ne_zero hn hr))).symm
  rw [inv_inv] at e
  exact (paper_equiv hu δ d hd).trans e

end ZInQBlueprint.CurveChart
#print axioms ZInQBlueprint.CurveChart.regular_identity
#print axioms ZInQBlueprint.CurveChart.pole_affine
#print axioms ZInQBlueprint.CurveChart.pole_identity
#print axioms ZInQBlueprint.CurveChart.regular_equiv
#print axioms ZInQBlueprint.CurveChart.pole_equiv
#print axioms ZInQBlueprint.CurveChart.paper_regular_equiv
#print axioms ZInQBlueprint.CurveChart.paper_pole_equiv
