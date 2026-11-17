import TYZIsogeny
import ApplicationLemmas

namespace ZInQBlueprint.TYZ

noncomputable section
attribute [local instance] Classical.decEq

/-- The distinguished point and two properties from TYZ Theorem 3.5(1) and
Lemma 3.18. The isogeny is now the fixed, proved homomorphism. -/
structure GenusPoint (d : ℕ) where
  point : genusCurve.toAffine.Point
  torsion_four : ∀ k : ℕ, 0 < k → k • point = 0 → (4:ℕ) • point = 0
  double_minus : tyzIsogeny ((2:ℕ) • point) = 0 ∨
    ∃ (u v : ℚ) (h : Rank.baseCurve.toAffine.Nonsingular
      (u : Rank.Qbar) ((v : Rank.Qbar)*Rank.sqrtMinus d)),
      WeierstrassCurve.Affine.Point.some _ _ h = tyzIsogeny ((2:ℕ) • point)

def GenusPoint.geometry {d : ℕ} (G : GenusPoint d) : GenusPointGeometry d :=
  ⟨G.point, tyzIsogeny, tyzIsogeny_kernel_two, G.torsion_four, G.double_minus⟩

def gaussianI : Zsqrtd (-1) := ⟨0,1⟩

/-- The printed phase in the first coefficient has a fixed sign in this residue class. -/
theorem gaussianPhase {d : ℕ} (hd : d % 8 = 5) : gaussianI^((d-1)/2) = -1 := by
  have h2 : gaussianI^2 = -1 := by decide
  have h4 : gaussianI^4 = 1 := by decide
  have h : (d-1)/2 = 4*(d/8)+2 := by omega
  rw [h,pow_add,pow_mul,h4,one_pow,one_mul,h2]

/-- Twice the lattice relation of p. 760, for the actual second coefficient.
The integer a is the first coefficient. Its value is immaterial to this implication. -/
def GaussianPeriodRelation {d : ℕ} (hd : d % 8 = 5) (P : genusCurve.toAffine.Point) (a : ℤ) : Prop :=
  Exceptional d P → ∃ z : Zsqrtd (-1),
    (a : Zsqrtd (-1))*gaussianI^((d-1)/2)*⟨1,-1⟩ +
      (printedCoefficient d hd : Zsqrtd (-1)) = 2*z

theorem periodParity_of_gaussianRelation {d : ℕ} (hd : d % 8 = 5) (G : GenusPoint d)
    (a : ℤ) (hPeriod : GaussianPeriodRelation hd G.point a) : PeriodParity hd G.geometry := by
  intro hEx
  obtain ⟨z,hz⟩ := hPeriod hEx
  have normOne : (gaussianI^((d-1)/2)).re^2+(gaussianI^((d-1)/2)).im^2=1 := by
    rw [gaussianPhase hd]
    decide
  have hEven := (ZInQBlueprint.gaussian_period_parity a (printedCoefficient d hd)
    (gaussianI^((d-1)/2)) z normOne (by simpa only [Int.cast_natCast] using hz)).2
  have hn : 2 ∣ printedCoefficient d hd := by exact_mod_cast hEven
  exact even_iff_two_dvd.mpr hn

theorem publicRank_of_genusPointPeriods
    (G : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GenusPoint d) (a : ℕ → ℤ)
    (hPeriod : ∀ d (hd : d % 8 = 5) (hs : Squarefree d),
      GaussianPeriodRelation hd (G d hd hs).point (a d)) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  publicRank_of_periodParity (fun d hd hs => (G d hd hs).geometry)
    (fun d hd hs => periodParity_of_gaussianRelation hd (G d hd hs) (a d) (hPeriod d hd hs))

theorem frozen_of_genusPointPeriods (hHeight : ZInQ.SixContactMin)
    (G : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GenusPoint d) (a : ℕ → ℤ)
    (hPeriod : ∀ d (hd : d % 8 = 5) (hs : Squarefree d),
      GaussianPeriodRelation hd (G d hd hs).point (a d)) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    hHeight (publicRank_of_genusPointPeriods G a hPeriod)

#print axioms gaussianPhase
#print axioms periodParity_of_gaussianRelation
#print axioms publicRank_of_genusPointPeriods
#print axioms frozen_of_genusPointPeriods

end
end ZInQBlueprint.TYZ
