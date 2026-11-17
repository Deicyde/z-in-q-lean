import TYZSpecialization

/-! The doubling test for the second coefficient in TYZ, journal p. 760.
All cusps and the genus representative belong to the actual source curve. -/
namespace ZInQBlueprint.TYZ.Specialization

noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine
abbrev A := genusCurve.toAffine.Point

/-- The real cusp τ(1/2), in the rational model Y² = X³ + 4X, up to sign. -/
def realCusp : A := .some 2 4 (by norm_num [nonsingular_iff, equation_iff, genusCurve])

/-- The unique nonzero rational point of order two, τ(1). -/
def twiceCusp : A := .some 0 0 (by norm_num [nonsingular_iff, equation_iff, genusCurve])

theorem twice_realCusp : (2:ℕ) • realCusp = twiceCusp := by
  rw [two_nsmul, realCusp]
  erw [Point.add_self_of_Y_ne (W := genusCurve.toAffine) (x₁ := 2) (y₁ := 4) (by norm_num [negY,genusCurve])]
  unfold twiceCusp
  erw [Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope, addX, addY, negAddY, negY, genusCurve]

theorem twice_twiceCusp : (2:ℕ) • twiceCusp = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (by norm_num [twiceCusp, negY, genusCurve])

theorem twiceCusp_ne_zero : twiceCusp ≠ 0 := Point.some_ne_zero _

/-- The unique nonzero rational point of order two on the normalized source.
It identifies `2τ(1/2)` without choosing between the two real order-four cusps. -/
theorem rational_two_torsion {x y : ℚ} (h : genusCurve.toAffine.Nonsingular (x : K) (y : K))
    (hP : (2:ℕ) • (Point.some _ _ h : A) = 0) : Point.some _ _ h = twiceCusp := by
  rw [two_nsmul] at hP
  have hy : (y : K) = 0 := by
    by_contra hn
    have hne : (y : K) ≠ genusCurve.toAffine.negY x y := by
      intro he
      simp [negY, genusCurve] at he
      exact hn (by linear_combination he / 2)
    rw [Point.add_self_of_Y_ne hne] at hP
    exact Point.some_ne_zero _ hP
  have hc : (y:K)^2 = (x:K)^3+4*x := by simpa [equation_iff,genusCurve] using h.1
  have hz : (x:K)^3+4*x = 0 := by rw [←hc,hy]; norm_num
  have hr : x^3+4*x = 0 := by exact_mod_cast hz
  have factor : x*(x^2+4)=0 := by linear_combination hr
  have hx := (mul_eq_zero.mp factor).resolve_right (by positivity : x^2+4 ≠ 0)
  simp [twiceCusp, hx, hy]

/-- A point with rational coordinates or the identity is rational over ℚ. -/
def RationalGenusPoint (P : A) : Prop :=
  P = 0 ∨ ∃ (x y : ℚ) (h : genusCurve.toAffine.Nonsingular (x:K) (y:K)), Point.some _ _ h = P

theorem identify_second_cusp {V : A} (hRat : RationalGenusPoint ((2:ℕ) • V))
    (h4 : (4:ℕ) • V = 0) (h2 : (2:ℕ) • V ≠ 0) : (2:ℕ) • V = twiceCusp := by
  obtain (hz | ⟨x,y,h,he⟩) := hRat
  · exact False.elim (h2 hz)
  · rw [←he]
    apply rational_two_torsion h
    rw [he, ←mul_nsmul]
    exact h4

/-- Doubling the trace isolates the second period. The torsion exponent on the
ambient field is only used for the error point `Y`. -/
theorem even_of_trace_identity {M : Type*} [AddCommGroup M] {U V C Y : M} {a k : ℤ} {b : ℕ}
    (hU : (2:ℕ) • U = 0) (hV : (2:ℕ) • V = C) (hC : (2:ℕ) • C = 0) (hne : C ≠ 0)
    (hTorsion : ∀ m : ℕ, 0 < m → m • Y = 0 → (4:ℕ) • Y = 0)
    (hTrace : a • U + b • V = (2:ℕ) • Y + k • C) : Even b := by
  have hV4 : (4:ℕ) • V = 0 := by rw [show (4:ℕ)=2*2 by decide, mul_nsmul,hV,hC]
  have hU4 : (4:ℕ) • U = 0 := by rw [show (4:ℕ)=2*2 by decide, mul_nsmul,hU,nsmul_zero]
  have hC4 : (4:ℕ) • C = 0 := by rw [show (4:ℕ)=2*2 by decide, mul_nsmul,hC,nsmul_zero]
  have h8 : (8:ℕ) • Y = 0 := by
    have f : (4:ℕ) • (a • U + b • V) = (4:ℕ) • ((2:ℕ) • Y + k • C) := congrArg _ hTrace
    simp only [smul_add, smul_comm (4:ℕ) a, smul_comm (4:ℕ) b, smul_comm (4:ℕ) k,
      hV4,hU4,hC4,smul_zero,add_zero,←mul_nsmul] at f
    exact f.symm
  have h4 := hTorsion 8 (by decide) h8
  have f : (2:ℕ) • (a • U + b • V) = (2:ℕ) • ((2:ℕ) • Y + k • C) := congrArg _ hTrace
  simp only [smul_add, smul_comm (2:ℕ) a, smul_comm (2:ℕ) b, smul_comm (2:ℕ) k,
    hU,hV,hC,smul_zero,zero_add,add_zero,←mul_nsmul] at f
  have hb : b • C = 0 := f.trans h4
  by_contra he
  obtain ⟨m,hm⟩ := Nat.not_even_iff_odd.mp he
  have hmul : (2*m) • C = 0 := by
    calc (2*m) • C = m • ((2:ℕ) • C) := by rw [←mul_nsmul, Nat.mul_comm]
         _ = 0 := by rw [hC,nsmul_zero]
  rw [hm, add_nsmul, one_nsmul, hmul, zero_add] at hb
  exact hne hb

/-- The period membership before the last parity inference on journal p. 760.
`F` is the subgroup of points defined over the compositum (or a subgroup
stable under the required trace); its torsion bound is used only there. -/
def TraceAtTorsion {d : ℕ} (hd : d % 8 = 5) (P : A) (F : AddSubgroup A) : Prop :=
  (4:ℕ) • P = 0 → ∃ (a k : ℤ) (U V : A) (Y : F), (2:ℕ) • U = 0 ∧
    (2:ℕ) • V = twiceCusp ∧ a • U + printedCoefficient d hd • V = (2:ℕ) • (Y:A) + k • twiceCusp

/-- The source-field torsion exponent, the Galois statement of TYZ 3.5(1)
and the displayed trace membership at torsion suffice for the actual rank conclusion. -/
theorem antiPoint_of_trace {d : ℕ} (hd : d % 8 = 5) (hs : Squarefree d)
    (F : AddSubgroup A) (P : F)
    (hTorsion : ∀ Y : F, ∀ m : ℕ, 0 < m → m • Y.val = 0 → (4:ℕ) • Y.val = 0)
    (hMinus : GaloisMinus d (tyzIsogeny ((2:ℕ) • P.val)))
    (hTrace : TraceAtTorsion hd P.val F) (hOdd : ZInQ.RouteK.Rank5b.T5bCl d = 1) : Rank.AntiPoint d := by
  have hinf : Rank.InfiniteOrder P.val := by
    intro m hm hz
    obtain ⟨a,k,U,V,Y,hU,hV,htrace⟩ := hTrace (hTorsion P m hm hz)
    have he := even_of_trace_identity hU hV twice_twiceCusp twiceCusp_ne_zero (hTorsion Y) htrace
    have hzero := he.natCast_zmod_two
    rw [printedCoefficient_mod_two hd hs,hOdd] at hzero
    exact one_ne_zero hzero
  have hImage := Rank.image_double_infinite tyzIsogeny tyzIsogeny_kernel_two _ hinf
  obtain (hz | ⟨u,v,hp,he⟩) := (minus_iff_coordinates (by omega : 0 < d) _).mp hMinus
  · exact False.elim (hImage 1 (by decide) (by simpa using hz))
  · rw [←he] at hImage
    exact ⟨u,v,hp,hImage⟩

/-- The published inputs for one value of `d`. The trace identity is required
only under the assumption that four times its very same representative vanishes. -/
structure TraceData (d : ℕ) (hd : d % 8 = 5) where
  fieldPoints : AddSubgroup A
  representative : fieldPoints
  torsion_four : ∀ Y : fieldPoints, ∀ m : ℕ, 0 < m → m • Y.val = 0 → (4:ℕ) • Y.val = 0
  double_minus : GaloisMinus d (tyzIsogeny ((2:ℕ) • representative.val))
  period : TraceAtTorsion hd representative.val fieldPoints

theorem publicRank_of_traces
    (h : ∀ d (hd : d % 8 = 5), Squarefree d → Nonempty (TraceData d hd)) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro d hd hs hOdd
  obtain ⟨D⟩ := h d hd hs
  exact antiPoint_of_trace hd hs D.fieldPoints D.representative D.torsion_four D.double_minus D.period hOdd

theorem frozen_of_traces (hHeight : ZInQ.SixContactMin)
    (h : ∀ d (hd : d % 8 = 5), Squarefree d → Nonempty (TraceData d hd)) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    hHeight (publicRank_of_traces h)

#print axioms twice_realCusp
#print axioms twice_twiceCusp
#print axioms rational_two_torsion
#print axioms identify_second_cusp
#print axioms even_of_trace_identity
#print axioms antiPoint_of_trace
#print axioms publicRank_of_traces
#print axioms frozen_of_traces
end
end ZInQBlueprint.TYZ.Specialization
