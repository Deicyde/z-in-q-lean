import BinaryCover
import IntegralComparison
import ChartSplitting

/-! The two choices of the affine chart of the six-contact curve. -/

open CategoryTheory AlgebraicGeometry Polynomial
open ZInQBlueprint.IntegralSextic ZInQBlueprint.DirectCharts ZInQBlueprint.LeadingOrders
open ZInQBlueprint.ResidualFactors ZInQBlueprint.GlobalTwist ZInQBlueprint.RationalClusters
open ZInQBlueprint.PrimitiveParameters ZInQBlueprint.GoodReductionCharts ZInQBlueprint.CurveChart

namespace ZInQBlueprint.BinaryCover

noncomputable section
set_option maxHeartbeats 1200000

theorem form_homogeneous {R : Type*} [CommRing R] (a b c x z : R) :
    form a b (c*x) (c*z) = c^6 * form a b x z := by
  unfold form alpha beta gamma
  ring

/-- The chart at z=1 or at x=1 of the fixed twisted rational equation, after
extension of scalars to K. The latter chart uses z=Z/X as its parameter. -/
def fixed (K : Type) [Field K] [CharZero K] (u : ℚ) (infinity : Bool) : K[X] :=
  integralEquation (C (delta u : K)) (C (u.num : K)) (C (u.den : K))
    (if infinity then 1 else X) (if infinity then X else 1)

def paper (K : Type) [Field K] [CharZero K] (u : ℚ) (infinity : Bool) : K[X] :=
  C (delta u : K) * MvPolynomial.eval₂ ((C : K →+* K[X]).comp (Rat.castHom K))
    ![if infinity then (1 : K[X]) else X, if infinity then X else 1] (paperSextic u)

theorem paper_eq {K : Type} [Field K] [CharZero K] (u : ℚ) (i : Bool) :
    paper K u i = C (yScale u : K)^2 * fixed K u i := by
  let x : K[X] := if i then 1 else X
  let z : K[X] := if i then X else 1
  let ψ := MvPolynomial.eval₂Hom ((C : K →+* K[X]).comp (Rat.castHom K)) ![x,z]
  have hi : ψ (MvPolynomial.C (u.num : ℚ)) = C (u.num : K) := by simp [ψ]
  have hn : ψ (MvPolynomial.C (u.den : ℚ)) = C (u.den : K) := by simp [ψ]
  have H : ψ (integralPolynomial u) =
      integralEquation 1 (C (u.num : K)) (C (u.den : K)) x z := by
    change ψ (integralEquation 1 _ _ _ _) = _
    simp only [integralEquation, form, m, n, alpha, beta, gamma, poleForm,
      map_add, map_mul, map_sub, map_pow, map_neg, map_ofNat, map_one]
    have HX : ψ (MvPolynomial.X 0) = x := by simp [ψ]
    have HZ : ψ (MvPolynomial.X 1) = z := by simp [ψ]
    simp only [HX, HZ, hi, hn]
  change C (delta u : K)*ψ (paperSextic u) = _
  rw [paper_integral_polynomial, map_mul, map_pow, H]
  have c : ψ (MvPolynomial.C (yScale u)) = C (yScale u : K) := by simp [ψ]
  rw [c]
  change C (delta u : K)*(_^2*integralEquation 1 _ _ x z) = _^2*integralEquation _ _ _ x z
  unfold integralEquation
  ring

def paperChartIso {K : Type} [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    SpecOver (R := K) (Cover (fixed K u i)) ≅ SpecOver (Cover (paper K u i)) := by
  let d : Kˣ := Units.mk0 (yScale u : K) (by exact_mod_cast yScale_ne hu)
  let scale : K[X]ˣ := Units.map (C : K →+* K[X]) d
  have H : (AlgEquiv.refl : K[X] ≃ₐ[K] K[X]) (paper K u i) =
      (scale : K[X])^2 * fixed K u i := paper_eq u i
  let e := squareEquiv (f := paper K u i) (g := fixed K u i)
    (AlgEquiv.refl : K[X] ≃ₐ[K] K[X]) scale H
  exact specIso e

variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]
local notation "Kp" => ℚ_[p]

private theorem map_chart' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (d g v a t : R) :
    (chart d g v a t).map φ = chart (φ d) (φ g) (φ v) (φ a) (φ t) := by
  simp [chart, monic_coeffs, map_ofNat]

private theorem factorization (u : ℚ) (v a : Zpˣ) (t : Zp) (x z : Kp[X])
    (hc : Coordinates p u t (v : Zp) (a : Zp)) :
    let φ := (C : Kp →+* Kp[X]).comp (algebraMap Zp Kp)
    let d := C (delta u : Kp)
    let b := C (u.num : Kp)
    let c := C (u.den : Kp)
    let rhs := -6*d*poleForm b c*φ (v : Zp)*(φ (a : Zp))^2*form 1 (φ t) x z
    (v = 1 ∧ integralEquation d b c x z = rhs) ∨
      ((v : Zp) = 8 ∧ integralEquation d b c (6*z) x = rhs) := by
  let φ := (C : Kp →+* Kp[X]).comp (algebraMap Zp Kp)
  have hm : φ (left p u) = m (C (u.num : Kp)) (C (u.den : Kp)) := by
    simp [φ, left, m, map_ofNat, -PadicInt.algebraMap_apply]
  have hn : φ (right p u) = n (C (u.num : Kp)) (C (u.den : Kp)) := by
    simp [φ, right, n, map_ofNat, -PadicInt.algebraMap_apply]
  cases hc with
  | first hv ha ht =>
    have h1 : φ (v : Zp) = 1 := by rw [hv, map_one]
    have h2 := (congrArg φ ht).trans hn
    rw [map_mul] at h2
    refine Or.inl ⟨Units.ext hv, ?_⟩
    change integralEquation _ _ _ x z = _ * form 1 (φ t) x z
    rw [integralEquation, ← hm, ← h2, ← ha, affine]
    change _ = -6*_ * _ * φ (v : Zp)*_ * _
    rw [h1]; ring
  | second hv ha ht =>
    have h8 : φ (v : Zp) = 8 := by rw [hv, map_ofNat]
    have h2 := congrArg φ ht
    rw [map_mul, map_mul, map_ofNat, hm] at h2
    refine Or.inr ⟨hv, ?_⟩
    change integralEquation _ _ _ (6*z) x = _ * form 1 (φ t) x z
    rw [integralEquation, ← hn, ← ha, reciprocal_chart h2.symm]
    change _ = -6*_ * _ * φ (v : Zp)*_ * _
    rw [h8]; ring

def sixUnit : Kpˣ := Units.mk0 6 (by norm_num)

theorem local_chart_equations (u : ℚ) (v a : Zpˣ) (t : Zp)
    (hc : Coordinates p u t (v : Zp) (a : Zp)) :
    polynomial p u v a t = fixed Kp u false ∨
    (dilate (sixUnit p)) (polynomial p u v a t) = C (6 : Kp)^6 * fixed Kp u true := by
  let φ := (C : Kp →+* Kp[X]).comp (algebraMap Zp Kp)
  have P : polynomial p u v a t =
    -6*C (delta u : Kp)*poleForm (C (u.num : Kp)) (C (u.den : Kp))*
      φ (v : Zp)*(φ (a : Zp))^2*form 1 (φ t) X 1 := by
    rw [polynomial, map_chart']
    simp [φ, chart, monicSextic, G, poleForm, map_ofNat, -PadicInt.algebraMap_apply]
  cases hc with
  | first hv ha ht =>
    left
    rw [P]
    rcases factorization p u v a t X 1 (.first hv ha ht) with ⟨_, H⟩ | ⟨wrong, _⟩
    · exact H.symm
    · rw [hv] at wrong; norm_num at wrong
  | second hv ha ht =>
    right
    rcases factorization p u v a t (C (6 : Kp)*X) 1 (.second hv ha ht) with ⟨wrong, _⟩ | ⟨_, H⟩
    · have hw : (v : Zp) = 1 := congrArg Units.val wrong
      rw [hv] at hw; norm_num at hw
    · have D : dilate (sixUnit p) (polynomial p u v a t) =
          -6*C (delta u : Kp)*poleForm (C (u.num : Kp)) (C (u.den : Kp))*
           φ (v : Zp)*(φ (a : Zp))^2*form 1 (φ t) (C (6 : Kp)*X) 1 := by
        rw [P]
        simp [φ, form, alpha, beta, gamma, poleForm, map_ofNat, sixUnit]
      rw [D, ← H]
      have hom := form_homogeneous
        (m (C (u.num : Kp)) (C (u.den : Kp))) (n (C (u.num : Kp)) (C (u.den : Kp)))
        (C (6 : Kp)) 1 X
      simp only [mul_one, map_ofNat] at hom ⊢
      simp only [fixed, ite_true, integralEquation]
      rw [hom]; ring

/-- Each DDMM chart is an affine chart of the paper's fixed twisted sextic,
over Q_p itself. In the reciprocal chart the pullback on coordinates sends
x to 6z and y to 6³w in the integral model. -/
theorem local_paper_chart_iso {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : Zpˣ) (t : Zp) (hc : Coordinates p u t (v : Zp) (a : Zp)) :
    ∃ i : Bool, Nonempty (SpecOver (R := Kp) (Cover (polynomial p u v a t)) ≅
        SpecOver (Cover (paper Kp u i))) := by
  rcases local_chart_equations p u v a t hc with direct | reciprocal
  · exact ⟨false, ⟨(eqToIso (congrArg (fun f : Kp[X] => SpecOver (R := Kp) (Cover f)) direct))
      ≪≫ paperChartIso hu false⟩⟩
  · let y : Kp[X]ˣ := Units.map (C : Kp →+* Kp[X]) ((sixUnit p)^3)
    have hy : (y : Kp[X])^2 = (C (6 : Kp))^6 := by
      change (C ((6 : Kp)^3))^2 = (C (6 : Kp))^6
      rw [map_pow, ← pow_mul]
    let e := squareEquiv (f := polynomial p u v a t) (g := fixed Kp u true) (dilate (sixUnit p)) y
      (by rw [hy]; exact reciprocal)
    exact ⟨true, ⟨(specIso e).symm ≪≫ paperChartIso hu true⟩⟩

end
end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.form_homogeneous
#print axioms ZInQBlueprint.BinaryCover.paperChartIso
#print axioms ZInQBlueprint.BinaryCover.local_chart_equations
#print axioms ZInQBlueprint.BinaryCover.local_paper_chart_iso
