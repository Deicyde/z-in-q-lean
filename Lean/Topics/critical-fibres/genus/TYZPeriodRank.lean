import TYZBracket
import PublicRankFromAnti

/-! Mathematical boundary for the second bracket of Tian--Yuan--Zhang, p. 760. -/

namespace ZInQBlueprint.TYZ

noncomputable section
attribute [local instance] Classical.decEq

/-- A short Weierstrass equation for A : 2v² = u³ + u, with X=2u and Y=4v. -/
def genusCurve : WeierstrassCurve Rank.Qbar := ⟨0, 0, 0, 4, 0⟩

theorem normalizedGenusEquation (u v : Rank.Qbar) :
    2*v^2 = u^3+u ↔ (4*v)^2 = (2*u)^3+4*(2*u) := by
  constructor <;> intro h
  · linear_combination 8*h
  · linear_combination h/8

/-- Cleared affine identity for (X,Y) ↦ ((X²+4)/(4X), Y(X²−4)/(8X²)). -/
theorem isogeny_identity {x y : Rank.Qbar} (h : y^2=x^3+4*x) :
    y^2*(x^2-4)^2 = x*((x^2+4)^3-16*x^2*(x^2+4)) := by rw [h]; ring

/-- The minus group on the normalized A, including the point at infinity.
For K=ℚ(√−d) a nonzero minus point has x=u and y=v√−d. -/
def InMinusGenus (d : ℕ) (Q : genusCurve.toAffine.Point) : Prop :=
  Q = 0 ∨ ∃ (u v : ℚ) (h : genusCurve.toAffine.Nonsingular
    (u : Rank.Qbar) ((v : Rank.Qbar)*Rank.sqrtMinus d)),
    WeierstrassCurve.Affine.Point.some _ _ h = Q

/-- The exceptional set A(K)^- + A[4] used in the displayed coefficient calculation. -/
def Exceptional (d : ℕ) (P : genusCurve.toAffine.Point) : Prop :=
  ∃ Q t : genusCurve.toAffine.Point, InMinusGenus d Q ∧ (4:ℕ) • t = 0 ∧ Q + t = P

/-- The geometric inputs from TYZ, with actual elliptic groups over ℚbar.
The affine conclusion deliberately allows the identity in the torsion case. -/
structure GenusPointGeometry (d : ℕ) where
  point : genusCurve.toAffine.Point
  phi : genusCurve.toAffine.Point →+ Rank.baseCurve.toAffine.Point
  kernel_two : ∀ Q, phi Q = 0 → (2:ℕ) • Q = 0
  torsion_four : ∀ k : ℕ, 0 < k → k • point = 0 → (4:ℕ) • point = 0
  double_minus : phi ((2:ℕ) • point) = 0 ∨
    ∃ (u v : ℚ) (h : Rank.baseCurve.toAffine.Nonsingular
      (u : Rank.Qbar) ((v : Rank.Qbar)*Rank.sqrtMinus d)),
      WeierstrassCurve.Affine.Point.some _ _ h = phi ((2:ℕ) • point)

/-- The evenness assertion for the *second* bracket, under the hypothesis
actually used in the proof of Theorem 3.5(2) on p. 760. -/
def PeriodParity {d : ℕ} (hd : d % 8 = 5) (G : GenusPointGeometry d) : Prop :=
  Exceptional d G.point → Even (printedCoefficient d hd)

/-- With the period calculation and its geometric inputs, an odd public
class-group sum gives a rationally anti-invariant point of infinite order. -/
theorem antiPoint_of_periodParity {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d)
    (G : GenusPointGeometry d) (hParity : PeriodParity hd G)
    (hSum : ZInQ.RouteK.Rank5b.T5bCl d = 1) : Rank.AntiPoint d := by
  have hOdd : (printedCoefficient d hd : ZMod 2) = 1 :=
    (printedCoefficient_mod_two hd hs).trans hSum
  have hinf : Rank.InfiniteOrder G.point := by
    intro k hk hzero
    have hEx : Exceptional d G.point := ⟨0, G.point, Or.inl rfl, G.torsion_four k hk hzero, zero_add _⟩
    have heven := (hParity hEx).natCast_zmod_two
    exact zero_ne_one (heven.symm.trans hOdd)
  have hImage := Rank.image_double_infinite G.phi G.kernel_two G.point hinf
  rcases G.double_minus with hzero | ⟨u,v,h,heq⟩
  · exact False.elim (hImage 1 (by decide) (by simpa only [one_nsmul] using hzero))
  · rw [← heq] at hImage
    exact ⟨u,v,h,hImage⟩

theorem publicRank_of_periodParity
    (G : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GenusPointGeometry d)
    (hParity : ∀ d (hd : d % 8 = 5) (hs : Squarefree d), PeriodParity hd (G d hd hs)) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro d hd hs
  exact antiPoint_of_periodParity hd hs (G d hd hs) (hParity d hd hs)

theorem frozen_of_periodParity (hHeight : ZInQ.SixContactMin)
    (G : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GenusPointGeometry d)
    (hParity : ∀ d (hd : d % 8 = 5) (hs : Squarefree d), PeriodParity hd (G d hd hs)) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    hHeight (publicRank_of_periodParity G hParity)

#print axioms normalizedGenusEquation
#print axioms isogeny_identity
#print axioms antiPoint_of_periodParity
#print axioms publicRank_of_periodParity
#print axioms frozen_of_periodParity

end
end ZInQBlueprint.TYZ
