import FixedData
import PaperScales
import ZInQKernel.Multiplication.Local.Dyadic

/-! Uniform nonvanishing of the degree-64 logarithm on the punctured cyclic group. -/
open WeierstrassCurve.Affine
namespace Sun28.FixedPreparation
open ZInQ ZInQ.Mult Sun28.Forward Sun28.WitnessIndices Sun28.Ordinary Sun28.Scalar
noncomputable section

/-- The two curve changes leave z unchanged up to the dyadic unit ε⁻². -/
theorem parameter_on_multiple (m : ℤ) :
    parameter (m • paperGenerator sqrt2_sq) =
    zCoord (A:=-genD^2) (m • genP0) / epsilon^2 := by
  let zAny {A : WeierstrassCurve.Affine K0} : A.Point → K0 := fun Q =>
    match Q with | .zero => 0 | .some x y _ => -x/y
  have source (b : K0) (Q : (curve b).Point) : parameter Q=zAny Q := by cases Q <;> rfl
  have model {A B : WeierstrassCurve.Affine K0} (e : A=B) (p : A.Point) (q : B.Point)
      (same : HEq p q) : zAny (m • p)=zAny (m • q) := by
    subst B; rw [eq_of_heq same]
  have id := model generator_cast.1 _ _ generator_cast.2
  rw [source,id,show curveGenerator=theta genP0 from theta_genP0.symm,←map_zsmul]
  cases q : m • genP0 with
  | zero =>
    change (0:K0)=0/epsilon^2
    rw [zero_div]
  | some x y h =>
    rw [theta_some]
    change -(epsilon^4*x)/(epsilon^6*y) = (-x/y)/epsilon^2
    by_cases hy : y=0
    · simp [hy]
    · field_simp [hy,epsilon_ne_zero]

theorem dyadic_parameter (m : ℤ) (nz : m≠0) :
    Vge vS 3 (parameter (m • paperGenerator sqrt2_sq)) ∧
    parameter (m • paperGenerator sqrt2_sq)≠0 := by
  rw [parameter_on_multiple]
  have old := zsmul_genP0_mem_formal m
  have ev : vS epsilon=0 := by rw [vP_apply prime_sqrt2Z epsilon_ne_zero,vS_epsilon]; rfl
  have ev2 : vS (epsilon^2)=0 := by rw [vS.map_pow,ev]; simp
  have oldDepth : Vge vS 3 (zCoord (A:=-genD^2) (m • genP0)) := old.2
  refine ⟨oldDepth.div_unit ev2,div_ne_zero ?_ (pow_ne_zero 2 epsilon_ne_zero)⟩
  intro z
  exact zsmul_genP0_ne_zero nz (zCoord_injOn vS_genA_nonneg old.1 (show (0:genCurve.toAffine.Point)∈W1 vS (-genD^2) from trivial)
    (z.trans zCoord_zero.symm))

private def tailTerm (b z : K0) (j : ℕ) :=
  (Nat.choose (2*(j+1)) (j+1):K0)*b^(j+1)*z^(4*(j+1))/(4*(j+1)+1:ℕ)

private theorem trunc_series (b z : K0) :
    logTrunc (shortDifferential b) 64 z=z*(1+∑ j ∈ Finset.range 15,tailTerm b z j) := by
  simp only [logTrunc,shortDifferential,tailTerm,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num
  ring

private theorem odd_nat_unit (j : ℕ) : vS ((4*j+1:ℕ):K0)=0 := by
  have n : 4*j+1≠0 := by omega
  have nz : ((4*j+1:ℕ):K0)≠0 := by exact_mod_cast n
  have odd : ¬2∣4*j+1 := by omega
  rw [vP_apply prime_sqrt2Z nz,vS_nat n,padicValNat.eq_zero_of_not_dvd odd]
  norm_num

theorem log64_dyadic {b z : K0} (bi : Vge vS 0 b) (deep : Vge vS 1 z) (nz : z≠0) :
    logTrunc (shortDifferential b) 64 z≠0 := by
  rw [trunc_series]
  apply mul_ne_zero nz (one_add_ne_zero (v:=vS) ?_)
  have term (j : ℕ) : Vge vS 1 (tailTerm b z j) := by
    have val := ((ZInQ.Mult.vge_natCast (v:=vS) ((2*(j+1)).choose (j+1))).mul (bi.pow (j+1))).mul (deep.pow (4*(j+1)))
    exact (val.mono (by push_cast; omega)).div_unit (odd_nat_unit (j+1))
  have sum (n : ℕ) : Vge vS 1 (∑ j ∈ Finset.range n, tailTerm b z j) := by
    induction n with
    | zero => simpa only [Finset.sum_range_zero] using (Vge.zero (v:=vS) 1)
    | succ n ih => rw [Finset.sum_range_succ]; exact ih.add (term n)
  exact sum 15

/-- Both translated and primary degree-64 denominators are nonzero whenever the index is. -/
theorem truncAt_multiple_nonzero (m : ℤ) (nz : m≠0) : truncAt (m • P)≠0 := by
  unfold truncAt
  rw [scalar_index]
  obtain ⟨deep,live⟩ := dyadic_parameter m nz
  have b : 0≤vS (-(3-sqrt2)^2) := by
    rw [←delta_eq,show -delta^2=Zs.toK0 (-deltaZ^2) by simp]
    exact vP_toK0_nonneg _ _
  exact log64_dyadic b (deep.mono (by decide)) live

/-- The nonconjugate and conjugate denominators in Sun's two-anchor test. -/
theorem both_denominators {w : NinePoints} {M : ℕ} {c : ℤ} {a : Labels} (rep : Consequences w M c a) :
    truncAt w.H≠0 ∧ conjugation (truncAt (translatedBase w c))≠0 := by
  constructor
  · rw [←rep.represented.h_point]
    exact truncAt_multiple_nonzero a.h rep.h_nonzero
  · rw [←rep.base_point,map_ne_zero]
    exact truncAt_multiple_nonzero (a.h-c) rep.base_nonzero

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.parameter_on_multiple
#print axioms Sun28.FixedPreparation.dyadic_parameter
#print axioms Sun28.FixedPreparation.log64_dyadic
#print axioms Sun28.FixedPreparation.truncAt_multiple_nonzero
#print axioms Sun28.FixedPreparation.both_denominators
