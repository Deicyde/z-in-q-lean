import ShortFormalSeries
import ZInQKernel.Multiplication.Local.FormalLogarithm

/-! Sun's chart on the actual formal-neighbourhood subgroup of the short curve. -/
namespace Sun28.ShortFormal
open ZInQ ZInQ.Mult Sun28.Ordinary Sun28.Scalar Sun28.ScalarTrace
open Filter Topology PowerSeries WithZero
open scoped NumberField
noncomputable section

variable {L : Type*} [Field L] [Valued L ℤᵐ⁰]

omit [Valued L ℤᵐ⁰] in
theorem order_eq (v : Valuation L ℤᵐ⁰) : discreteOrder v=ordOf v := by
  ext x
  by_cases zero : x=0
  · simp [zero]
  · rw [ordOf_apply v zero]
    change (if v x=0 then ⊤ else ((-WithZero.log (v x):ℤ):WithTop ℤ))=_
    rw [ite_eq_right ((Valuation.ne_zero_iff v).mpr zero)]

variable [CompleteSpace L] [DecidableEq L]

/-- Use the formal subgroup itself for the two carriers in the local chart. -/
def kernelChart {b : L} (hb : 0≤vK L b) : EllipticKernelChart (vK L) b where
  kernel := formalNbhd b hb
  membership := by
    intro P hx hp
    apply (mem_formalNbhd_iff hb P).2
    cases P with
    | zero => exact zero_mem_W1 _
    | some x y hy =>
      change 0<vK L x⁻¹ at hx
      have nz : x≠0 := by rintro rfl; exact hp (by simp [parameter])
      obtain ⟨m,hm⟩ := val_eq_coe (v:=vK L) nz
      rw [val_inv_coe hm] at hx
      change vK L x<0
      rw [hm]
      have hn : (0:ℤ)< -m := by exact_mod_cast hx
      exact_mod_cast (show m<0 by omega)
  F := ↥(formalNbhd b hb)
  addGroup := inferInstanceAs (AddCommGroup ↥(formalNbhd b hb))
  coordinate := fun P => zCoord P.val
  integral := fun P => P.2.2
  chart := AddEquiv.refl ↥(formalNbhd b hb)
  chart_parameter := by
    rintro ⟨P,hP⟩
    change zCoord P=parameter P
    cases P <;> rfl

/-- The logarithm on this same subgroup is the convergent elliptic logarithm
in the short Weierstrass parameter. -/
def kernelLog {p e : ℕ} [Fact p.Prime] (h : ResidueChar L p e) {b : L} (hb : 0≤vK L b) :
    (kernelChart hb).F →+ L where
  toFun := fun P => ellLog ((show ↥(formalNbhd b hb) from P).val)
  map_zero' := ellLog_zero
  map_add' := fun P Q => ellLog_add h hb ((mem_formalNbhd_iff hb _).1 P.2) ((mem_formalNbhd_iff hb _).1 Q.2)

/-- Sun counts terms from r=1, the published formal logarithm from r=0 with zero constant. -/
theorem trunc_eq {F : Type*} [Field F] (b t : F) (n : ℕ) :
    logTrunc (fun j => coeff (j-1) (shortF b)) n t =
      ∑ i ∈ Finset.range (n+1), logCoeffA b i * t^i := by
  induction n with
  | zero => simp [logTrunc,logCoeffA]
  | succ n ih =>
    unfold logTrunc at ih ⊢
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ (n:=n+1)]
    congr 1
    simp [shortF,invDiffSeries,logCoeffA,div_mul_eq_mul_div]

omit [DecidableEq L] in
theorem converges {p e : ℕ} [Fact p.Prime] (h : ResidueChar L p e) {b t : L}
    (hb : 0≤vK L b) (ht : 1≤vK L t) :
    Tendsto (fun n => logTrunc (fun j => coeff (j-1) (shortF b)) n t) atTop (𝓝 (evalLog b t)) := by
  simp_rw [trunc_eq]
  exact (summable_log h hb ht).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem generic_chart {p e : ℕ} [Fact p.Prime] (hp : ResidueChar L p e) [CharZero L]
    {b : L} (hb : 0≤vK L b) :
    ∃ T : EllipticKernelChart (vK L) b, ∃ A : T.F →+ L, ∃ U F : PowerSeries L,
      coeff 0 U=1 ∧ U^2-U+C b*X^4=0 ∧ 2*U*F=2*U-X*derivative U ∧
      ∀ Y : T.F, Tendsto (fun n => logTrunc (fun j => coeff (j-1) F) n (T.coordinate Y))
        atTop (𝓝 (A Y)) := by
  exact ⟨kernelChart hb,kernelLog hp hb,shortU b,shortF b,(unit_model b).1,(unit_model b).2,
    differential b,fun P => converges hp hb ((kernelChart hb).integral P)⟩

end
#print axioms order_eq
#print axioms kernelLog
#print axioms converges
#print axioms generic_chart
end Sun28.ShortFormal
