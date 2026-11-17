import LocalDiscs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Integral changes of variable as polynomial identities. -/
namespace ZInQBlueprint.DiscEquations
open Polynomial ZInQBlueprint.ClusterCharts ZInQBlueprint.LocalDiscs
open ZInQBlueprint.SexticCalibration
noncomputable section
variable {R : Type*} [CommRing R]

def zeroResidual (a U : R) : R[X] :=
  C (-4*(2*a+16)^3)*X^3 + C (U*slope₀ a)*X

def poleResidual (a U : R) : R[X] :=
  C 729 * (C (3*(2*a+2)^3)*X^3 + C (U*firstPole a))

def polePolynomial (w : R) : R[X] := pole X (C w)

/-- The normalized polynomial on a root disc at zero has integral coefficients. -/
theorem zero_chart {a : R} (ha : q₀ a = 0) (c U : R) :
    ∃ g e : R[X], (sextic (c^2*U)).comp (C a+C c*X) = C (c^3)*g ∧
      g = zeroResidual a U + C c*e := by
  have h : q₀ (C a) = 0 := by simpa [q₀, map_ofNat] using congrArg (C : R →+* R[X]) ha
  obtain ⟨e, he⟩ := zero_disc h (C c) (C U) (X : R[X])
  refine ⟨_, e, ?_, rfl⟩
  convert he using 1
  · simp [sextic,Polynomial.comp,eval₂_pow,map_ofNat]
  · simp [zeroResidual,slope₀,map_ofNat]
    ring

/-- At a pole we use w⁷ f(3Z/w), retaining the rational leading scalar separately. -/
theorem pole_chart {a : R} (ha : qPole a = 0) (c U : R) :
    ∃ g e : R[X], (polePolynomial (c^3*U)).comp (C a+C c*X) = C (c^3)*g ∧
      g = poleResidual a U + C c*e := by
  have h : qPole (C a) = 0 := by simpa [qPole,map_ofNat] using congrArg (C : R →+* R[X]) ha
  obtain ⟨e, he⟩ := pole_disc h (C c) (C U) (X : R[X])
  refine ⟨_, e, ?_, rfl⟩
  convert he using 1
  · simp [polePolynomial,pole,Polynomial.comp,eval₂_pow]
  · simp [poleResidual,firstPole,map_ofNat]
    ring

variable {k : Type*} [CommRing k]
theorem map_zeroResidual (φ : R →+* k) (a U : R) :
    (zeroResidual a U).map φ = zeroResidual (φ a) (φ U) := by
  simp [zeroResidual,slope₀,map_ofNat]

theorem map_poleResidual (φ : R →+* k) (a U : R) :
    (poleResidual a U).map φ = poleResidual (φ a) (φ U) := by
  simp [poleResidual,firstPole,map_ofNat]

theorem zero_chart_reduction (φ : R →+* k) {a c : R} (ha : q₀ a = 0) (hc : φ c = 0) (U : R) :
    ∃ g : R[X], (∀ y, (sextic (c^2*U)).eval (a+c*y) = c^3*g.eval y) ∧
      g.map φ = zeroResidual (φ a) (φ U) := by
  obtain ⟨g,e,h,hg⟩ := zero_chart ha c U
  refine ⟨g, ?_, ?_⟩
  · intro y
    simpa using congrArg (fun P : R[X] => P.eval y) h
  · simp [hg,hc,map_zeroResidual]

theorem pole_chart_reduction (φ : R →+* k) {a c : R} (ha : qPole a = 0) (hc : φ c = 0) (U : R) :
    ∃ g : R[X], (∀ y, (polePolynomial (c^3*U)).eval (a+c*y) = c^3*g.eval y) ∧
      g.map φ = poleResidual (φ a) (φ U) := by
  obtain ⟨g,e,h,hg⟩ := pole_chart ha c U
  refine ⟨g, ?_, ?_⟩
  · intro y
    simpa using congrArg (fun P : R[X] => P.eval y) h
  · simp [hg,hc,map_poleResidual]

private def sixTerms (a b c d e f g : R) : R[X] :=
  C a*X^6 + C b*X^5 + C c*X^4 - C d*X^3 + C e*X^2 + C f*X - C g

private theorem sixTerms_degree (a b c d e f g : R) :
    (sixTerms a b c d e f g).natDegree ≤ 6 := by
  unfold sixTerms
  compute_degree!

private theorem sixTerms_coeff (a b c d e f g : R) :
    (sixTerms a b c d e f g).coeff 6 = a := by
  simp [sixTerms,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow]

theorem zero_degree (s : R) : (sextic s).natDegree ≤ 6 := sixTerms_degree ..
theorem zero_lead (s : R) : (sextic s).coeff 6 = -4+3*s := sixTerms_coeff ..

private theorem polePolynomial_eq (w : R) :
    let t := 9-32*w^2
    polePolynomial w = sixTerms (729*(3-4*w)) (1458*t) (243*t*(28*w+9))
      (108*t^2) (27*t^2*(28*w-9)) (18*t^3) (t^3*(4*w+3)) := by
  simp [sixTerms,polePolynomial,pole,map_ofNat]

theorem pole_degree (w : R) : (polePolynomial w).natDegree ≤ 6 := by
  rw [polePolynomial_eq]
  exact sixTerms_degree ..

theorem pole_lead (w : R) : (polePolynomial w).coeff 6 = 729*(3-4*w) := by
  rw [polePolynomial_eq]
  exact sixTerms_coeff ..

end
end ZInQBlueprint.DiscEquations

#print axioms ZInQBlueprint.DiscEquations.zero_chart
#print axioms ZInQBlueprint.DiscEquations.pole_chart
#print axioms ZInQBlueprint.DiscEquations.map_zeroResidual
#print axioms ZInQBlueprint.DiscEquations.map_poleResidual
#print axioms ZInQBlueprint.DiscEquations.zero_chart_reduction
#print axioms ZInQBlueprint.DiscEquations.pole_chart_reduction
#print axioms ZInQBlueprint.DiscEquations.zero_degree
#print axioms ZInQBlueprint.DiscEquations.pole_degree
#print axioms ZInQBlueprint.DiscEquations.zero_lead
#print axioms ZInQBlueprint.DiscEquations.pole_lead
