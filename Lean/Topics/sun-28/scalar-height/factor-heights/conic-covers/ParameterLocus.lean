import ParameterCovers
import ScalarBranches

namespace Sun28.ConicCovers
open ZInQ ZInQ.Mult Height Sun28.FactorHeights Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation
open Sun28.WitnessHeight Sun28.ScalarLucas Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.IndexHeights Sun28.ScalarDepth Sun28.ScalarRankZero
noncomputable section

def positiveParameter (x:ℚ) : Prop :=
  ∃ r:ℚ, 4<r^2 ∧ ratSquare (7*(r^2-4)) ∧ ratSquare (16*r^2-15) ∧
    let n:=15-2*r^2; let D:=1-2*r^2
    (3*n^2+2398*D^2)*(x^2+3/2)=2401*D^2*x^2

def negativeParameter (x:ℚ) : Prop :=
  ∃ r:ℚ, r≠0 ∧ ratSquare (7*(5*r^2+8)) ∧ ratSquare (35*(8*r^2+3)) ∧
    343*(15+5*r^2)^2-439*(1+5*r^2)^2=(8*x*(1+5*r^2))^2

private theorem positive_lift {x:ℚ} (hc:positiveParameter x) : conics x 2 1 1 := by
  obtain ⟨r,gt,⟨A,eA⟩,⟨B,eB⟩,ex⟩:=hc
  let n:=15-2*r^2
  let D:=1-2*r^2
  have d:D≠0:=by dsimp [D];linarith
  let t:=n/D
  have nt:n=t*D:=by dsimp [t];field_simp
  have r0:r≠0:=by intro z;rw[z] at gt;norm_num at gt
  have ap:A≠0:=by intro z;rw [z] at eA;nlinarith
  have bp:B≠0:=by intro z;rw [z] at eB;nlinarith
  have nn:n≠0:=by
    intro z
    have h30:¬IsSquare (30:ℚ):=by
      rintro ⟨k,e⟩
      have zz:=(Rat.exists_mul_self 30).mp ⟨k,e.symm⟩
      norm_num [Rat.sqrt_ofNat,show Nat.sqrt 30=5 by symm;exact Nat.eq_sqrt.mpr (by decide)] at zz
    apply h30
    refine ⟨2*r,?_⟩
    dsimp [n] at z
    linear_combination 2*z
  have tn:t≠0:=div_ne_zero nn d
  let U:=4*A/D
  let V:=28*r*B/D
  have un:U≠0:=by dsimp [U];exact div_ne_zero (mul_ne_zero (by norm_num) ap) d
  have vn:V≠0:=by dsimp [V];exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) r0) bp) d
  have F:2*(1-t^2)=U^2:=by
    dsimp only [t,U];field_simp [d];dsimp only [n,D];linear_combination 16*eA
  have G:14*(225-t^2)=V^2:=by
    dsimp only [t,V];field_simp [d];dsimp only [n,D];linear_combination 784*r^2*eB
  change (3*n^2+2398*D^2)*(x^2+3/2)=2401*D^2*x^2 at ex
  rw [nt] at ex
  have mark:(3*t^2+2398)*(x^2+3/2)=2401*x^2:=by
    apply mul_left_cancel₀ (pow_ne_zero 2 d)
    linear_combination ex
  have F1:2*(x^2+3/2)*U^2=4802:=by
    linear_combination -(2*x^2+3)*F - 4/3*mark
  refine ⟨49/U,49*t/U,7*V/U,div_ne_zero (by norm_num) un,div_ne_zero (mul_ne_zero (by norm_num) tn) un,
    div_ne_zero (mul_ne_zero (by norm_num) vn) un,?_,?_,?_⟩
  · field_simp;linear_combination F1
  · field_simp;linear_combination F1/2+2401/2*F
  · field_simp;linear_combination 32*F1-343*F+49*G

private theorem negative_lift {x:ℚ} (hc:negativeParameter x) : conics x 14 (-35) 7 := by
  obtain ⟨r,rn,⟨A,eA⟩,⟨B,eB⟩,ex⟩:=hc
  let n:=15+5*r^2
  let D:=1+5*r^2
  have d:D≠0:=by dsimp [D];positivity
  let t:=n/D
  have tn:t≠0:=by dsimp [t,n,D];positivity
  have nt:n=t*D:=by dsimp [t];field_simp
  have an:A≠0:=by intro z;rw [z] at eA;nlinarith only [eA,sq_nonneg r]
  have bn:B≠0:=by intro z;rw [z] at eB;nlinarith only [eB,sq_nonneg r]
  let U:=2*A/D
  let V:=10*r*B/D
  have un:U≠0:=by dsimp [U];exact div_ne_zero (mul_ne_zero (by norm_num) an) d
  have vn:V≠0:=by dsimp [V];exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) rn) bn) d
  have F:t^2-1=U^2:=by dsimp [t,U,n,D];field_simp;linear_combination 4*eA
  have G:5*(225-t^2)=V^2:=by dsimp [t,V,n,D];field_simp;linear_combination 100*r^2*eB
  change 343*n^2-439*D^2=(8*x*D)^2 at ex
  rw [nt] at ex
  have mark:343*t^2-439=(8*x)^2:=by
    apply mul_left_cancel₀ (pow_ne_zero 2 d)
    linear_combination ex
  refine ⟨7*U/8,7*V/40,7*t,div_ne_zero (mul_ne_zero (by norm_num) un) (by norm_num),
    div_ne_zero (mul_ne_zero (by norm_num) vn) (by norm_num),mul_ne_zero (by norm_num) tn,?_,?_,?_⟩
  · linear_combination -mark/32+343/32*F
  · linear_combination -mark/64-343/320*G
  · linear_combination -mark

theorem positive_iff_parameter (x:ℚ) : conics x 2 1 1 ↔ positiveParameter x :=
  ⟨fun w=>by
    obtain ⟨r,b,A,B,_extra,mark⟩:=positive_parameter w
    exact ⟨r,b,A,B,mark⟩,positive_lift⟩

theorem negative_iff_parameter (x:ℚ) : conics x 14 (-35) 7 ↔ negativeParameter x :=
  ⟨negative_parameter,negative_lift⟩

def parameterLocus (x:ℚ) : Prop :=
  (¬∃i,concentrated x i) ∨
    (positiveParameter x ∧ allowance x<2*Real.log 1199+4*Real.log x.den+4) ∨
    (negativeParameter x ∧ allowance x<2*Real.log 35+2*Real.log x.den+4)

/-- Both directions retain the original scalar abscissa and its denominator test. -/
theorem reduced_iff_parameters (x:ℚ) : reducedLocus x ↔ parameterLocus x := by
  simp only [reducedLocus,parameterLocus,positive_iff_parameter,negative_iff_parameter]

/-- The accepted scalar soundness interface with the computed covers in place. -/
def ParameterExceptionalScalarBound : Prop :=
  ∀ (A:Fin 9→AffineInput) (x η:ℚ), ¬(∃k:ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x → parameterLocus x →
    x∈exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x)≤allowance x

theorem scalar_of_parameter_exceptions (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (est:ParameterExceptionalScalarBound) : ScalarBound := by
  apply scalar_of_reduced_exceptions descent reduction
  intro A x η ni cert hard loc box
  exact est A x η ni cert hard ((reduced_iff_parameters x).mp loc) box

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.positive_iff_parameter
#print axioms Sun28.ConicCovers.negative_iff_parameter
#print axioms Sun28.ConicCovers.reduced_iff_parameters
#print axioms Sun28.ConicCovers.scalar_of_parameter_exceptions
