import ChartConverse
import OrdinateCharts
import SunCertificate
import SunPublishedScalar

/-! Rational affine inputs, the published scalar generator and the integer labels. -/
namespace Sun28.WitnessIndices
open ZInQ WeierstrassCurve WeierstrassCurve.Affine Sun28.Ordinates
noncomputable section

/-- Convert the finite rational branch used for each affine ordinate into an actual point. -/
structure AffineInput where
  re : ℚ
  im : ℚ
  branch : Branch
  root : ℚ
  valid : branch.condition (ordinateReal re im) (ordinateRadical re im) root

def AffineInput.y (A : AffineInput) : K0 := A.branch.point (ordinateRadical A.re A.im) A.root

theorem AffineInput.onCurve (A : AffineInput) :
    curveC.toAffine.Equation (pair A.re A.im) A.y := by
  apply (curveC_equation_iff ..).2
  rw [delta_sq]
  exact (ordinate_charts A.re A.im A.y).2 ⟨A.branch,A.root,A.valid,rfl⟩

def AffineInput.point (A : AffineInput) : CPoint := Point.mk A.onCurve

theorem affine_represented {x y : K0} (h : curveC.toAffine.Nonsingular x y) :
    ∃ A : AffineInput, A.point = .some x y h := by
  obtain ⟨u,v⟩ := x
  have eq := (curveC_equation_iff _ _).1 h.1
  rw [delta_sq] at eq
  obtain ⟨b,t,e,ey⟩ := (ordinate_charts u v y).1 eq
  refine ⟨⟨u,v,b,t,e⟩,?_⟩
  simp only [AffineInput.point,AffineInput.y,Point.mk,Point.some.injEq]
  exact ⟨rfl,ey.symm⟩

/-- Every signed multiple is the double of an affine input, including zero. -/
theorem affine_double_surjective (k : ℤ) :
    ∃ A : AffineInput, (2:ℕ) • A.point = k • P := by
  have dbl : (2:ℕ) • (k • pointR) = k • P := by rw [P,two_nsmul,two_nsmul,zsmul_add]
  cases e : k • pointR with
  | zero =>
    have tors := (curveC_two_torsion cT0).2 (Or.inr (Or.inl rfl))
    obtain ⟨A,eA⟩ := affine_represented (equation_iff_nonsingular.mp curveC_equation_zero)
    have eT : A.point = cT0 := eA
    refine ⟨A,?_⟩
    rw [eT,tors,←dbl,e]
    exact (nsmul_zero ..).symm
  | some x y hx =>
    obtain ⟨A,eA⟩ := affine_represented hx
    exact ⟨A,by rw [eA,←dbl,e]⟩

/-- Sun's actual nine independent x-coordinate pairs and finite rational ordinate choices.
Positions 0,1,2,3,4 give Q,N,T,Z,H; 5–8 give the four U's. -/
def nineAffine (A : Fin 9 → AffineInput) : NinePoints where
  Q := (A 0).point
  N := (A 1).point
  T := (A 2).point
  Z := (A 3).point
  H := (A 4).point
  U := fun i => (A ⟨i.val+5,by omega⟩).point

theorem indices_of_rational_charts (A : Fin 9 → AffineInput) (c : ℤ)
    {D K S : ℝ} (hD : 0≤D) (hS : 0≤S) (guards : Guards (nineAffine A).doubles c) :
    ∃! a : Labels, Consequences (nineAffine A).doubles (Sun28.multiplier D K S) c a := by
  obtain ⟨six,eight,-⟩ := Sun28.multiplier_spec (K:=K) hD hS
  exact extract_from_doubles _ _ _ (by omega) six guards

private def coeffEquiv {b b' : K0} (e : b=b') :
    (Sun28.Scalar.curve b).Point ≃+ (Sun28.Scalar.curve b').Point := by
  subst b'
  exact AddEquiv.refl _

private theorem coeffEquiv_some {b b' x y x' y' : K0} (e : b=b')
    (h : (Sun28.Scalar.curve b).Nonsingular x y) (h' : (Sun28.Scalar.curve b').Nonsingular x' y')
    (ex : x=x') (ey : y=y') :
    coeffEquiv e (.some x y h)=.some x' y' h' := by
  subst b' x' y'
  rfl

/-- Transfer to the exact group type used by the ordinary and scalar logarithm calculations. -/
def scalarEquiv : CPoint ≃+ (Sun28.Scalar.curve (-(3-sqrt2)^2)).Point :=
  coeffEquiv (b:= -delta^2) (by rw [delta_eq])

theorem scalarEquiv_generator : scalarEquiv P = Sun28.Scalar.paperGenerator sqrt2_sq := by
  rw [P,two_smul_pointR]
  apply coeffEquiv_some
  · rw [Sun28.Scalar.generatorX,twoRX_eq]; ring
  · rw [Sun28.Scalar.generatorY,twoRY_eq]; ring

theorem scalar_index (k : ℤ) :
    scalarEquiv (k • P)= k • Sun28.Scalar.paperGenerator sqrt2_sq := by
  rw [map_zsmul,scalarEquiv_generator]

theorem scalar_generator_infinite : addOrderOf (Sun28.Scalar.paperGenerator sqrt2_sq)=0 := by
  apply addOrderOf_eq_zero
  apply injective_zsmul_iff_not_isOfFinAddOrder.mp
  intro a b h
  exact index_injective (scalarEquiv.injective ((scalar_index a).trans (h.trans (scalar_index b).symm)))

/-- The signed multiple maps to the corresponding element of the normalized public carrier D. -/
theorem public_carrier_index (k : ℤ) :
    theta.symm (k • P) = (indexEquivCarrier k : genCurve.toAffine.Point) := normalized_index k

#print axioms AffineInput.onCurve
#print axioms affine_represented
#print axioms affine_double_surjective
#print axioms indices_of_rational_charts
#print axioms scalarEquiv_generator
#print axioms scalar_index
#print axioms scalar_generator_infinite
#print axioms public_carrier_index
end
end Sun28.WitnessIndices
