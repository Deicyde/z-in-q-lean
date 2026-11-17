import ProjectiveNegation

/-! The bihomogeneous polynomial law agrees with the group sum off the diagonal. -/
namespace Sun28.RealCharts
open WeierstrassCurve
open scoped WeierstrassCurve.Projective Sun28.RealCharts Topology
noncomputable section

private abbrev V := Fin 3 → ℝ
private abbrev rep : V → Plane := Quotient.mk (MulAction.orbitRel ℝˣ V)

set_option maxHeartbeats 1600000 in
theorem secant_polynomial_continuous (W : WeierstrassCurve ℝ) :
    Continuous (fun p : V × V => W.toProjective.addXYZ p.1 p.2) := by
  have x : Continuous (fun p : V × V => W.toProjective.addX p.1 p.2) := by
    unfold Projective.addX
    fun_prop
  have z : Continuous (fun p : V × V => W.toProjective.addZ p.1 p.2) := by
    unfold Projective.addZ
    fun_prop
  have y : Continuous (fun p : V × V => W.toProjective.negAddY p.1 p.2) := by
    unfold Projective.negAddY
    fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · exact x
  · change Continuous (fun p : V × V => -W.toProjective.negAddY p.1 p.2 -
      W.a₁ * W.toProjective.addX p.1 p.2 - W.a₃ * W.toProjective.addZ p.1 p.2)
    exact (y.neg.sub (continuous_const.mul x)).sub (continuous_const.mul z)
  · exact z

/-- The polynomial secant has a value in the full quotient on every input. -/
def secant (W : WeierstrassCurve ℝ) (p : Plane × Plane) : Plane :=
  Quotient.map₂ W.toProjective.addXYZ (by
    rintro u u' ⟨a,rfl⟩ v v' ⟨b,rfl⟩
    change W.toProjective.addXYZ ((a:ℝ) • u') ((b:ℝ) • v') ≈ W.toProjective.addXYZ u' v'
    rw [Projective.addXYZ_smul]
    exact Projective.smul_equiv _ ((a.isUnit.mul b.isUnit).pow 2)) p.1 p.2

theorem secant_continuous (W : WeierstrassCurve ℝ) : Continuous (secant W) := by
  have q : IsOpenQuotientMap rep := MulAction.isOpenQuotientMap_quotientMk
  apply (q.prodMap q).continuous_comp_iff.mp
  exact continuous_quotient_mk'.comp (secant_polynomial_continuous W)

private theorem secant_eq_group (W : WeierstrassCurve ℝ) (P Q : Plane) (ne : P≠Q) :
    W.toProjective.addMap P Q=secant W (P,Q) := by
  obtain ⟨p,rfl⟩ := Quotient.mk_surjective P
  obtain ⟨q,rfl⟩ := Quotient.mk_surjective Q
  rw [Projective.addMap_eq,Projective.add_of_not_equiv (fun e => ne (Quotient.sound e))]
  rfl

private theorem pointClass_injective (W : WeierstrassCurve ℝ) :
    Function.Injective (fun Q : W.toAffine.Point => Q.toProjective.point) := by
  intro P Q same
  apply (Projective.Point.toAffineAddEquiv W).symm.injective
  exact Projective.Point.ext_iff.mpr same

/-- Joint continuity holds at every pair of distinct nonsingular real points. -/
theorem off_diagonal (W : WeierstrassCurve ℝ) {P Q : W.toAffine.Point} (ne : P≠Q) :
    ContinuousAt (fun p : W.toAffine.Point × W.toAffine.Point => p.1+p.2) (P,Q) := by
  let _ := elliptic_t2Space W
  have inducing : Topology.IsInducing (fun R : W.toAffine.Point => R.toProjective.point) := ⟨rfl⟩
  apply inducing.continuousAt_iff.mpr
  have factors : Continuous (fun p : W.toAffine.Point × W.toAffine.Point =>
      (p.1.toProjective.point,p.2.toProjective.point)) :=
    ((projective_continuous W).comp continuous_fst).prodMk ((projective_continuous W).comp continuous_snd)
  apply ((secant_continuous W).comp factors).continuousAt.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds ne] with p hp
  change (p.1+p.2).toProjective.point = secant W (p.1.toProjective.point,p.2.toProjective.point)
  have eq : (p.1+p.2).toProjective=p.1.toProjective+p.2.toProjective :=
    (Projective.Point.toAffineAddEquiv W).symm.map_add _ _
  rw [eq,Projective.Point.add_point]
  exact secant_eq_group W _ _ (fun h => hp (pointClass_injective W h))

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.secant_polynomial_continuous
#print axioms Sun28.RealCharts.secant_continuous
#print axioms Sun28.RealCharts.off_diagonal
