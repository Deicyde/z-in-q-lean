import SecantLaw

/-! A translated secant avoids the diagonal in a neighborhood of each double. -/
namespace Sun28.RealCharts
open ZInQ WeierstrassCurve Sun28.Scalar Sun28.RealRatio
open scoped Sun28.RealCharts Topology
noncomputable section

/-- Two opposite translates extend continuity of the sum across the diagonal. -/
theorem addition_of_injective_orbit {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (g : G) (inj : Function.Injective (fun n : ℤ => n • g))
    (away : ∀ {a b : G}, a≠b →
      ContinuousAt (fun p : G × G => p.1+p.2) (a,b)) : ContinuousAdd G := by
  refine ⟨continuous_iff_continuousAt.mpr ?_⟩
  rintro ⟨a,b⟩
  by_cases eq : a=b
  · subst b
    let bad : Set ℤ := {0} ∪ (fun n : ℤ => n • g) ⁻¹' {a,-a}
    have finite : bad.Finite :=
      (Set.finite_singleton 0).union (((Set.finite_singleton (-a)).insert a).preimage inj.injOn)
    obtain ⟨n,hn⟩ := finite.exists_notMem
    have live : n≠0 ∧ n • g≠a ∧ n • g≠-a := by
      simpa only [bad,Set.mem_union,Set.mem_singleton_iff,Set.mem_preimage,Set.mem_insert_iff,
        not_or] using hn
    let t : G := n • g
    have left : a≠t := live.2.1.symm
    have right : a≠-t := fun e => live.2.2 (by rw [e,neg_neg])
    have distinct : a+t≠a+(-t) := by
      intro same
      have opposed : n • g=(-n) • g := by simpa only [neg_zsmul] using add_left_cancel same
      have := inj opposed
      omega
    have lt : ContinuousAt (fun p : G × G => p.1+t) (a,a) :=
      ContinuousAt.comp (f:=fun p : G × G => (p.1,t)) (away left)
        (continuous_fst.prodMk continuous_const).continuousAt
    have rt : ContinuousAt (fun p : G × G => p.2+(-t)) (a,a) :=
      ContinuousAt.comp (f:=fun p : G × G => (p.2,-t)) (away right)
        (continuous_snd.prodMk continuous_const).continuousAt
    have sum : ContinuousAt (fun p : G × G => (p.1+t)+(p.2+(-t))) (a,a) :=
      ContinuousAt.comp (f:=fun p : G × G => (p.1+t,p.2+(-t))) (away distinct) (lt.prodMk rt)
    simpa only [add_add_add_comm,add_neg_cancel,add_zero] using sum
  · exact away eq

theorem continuous_add_factor (σ : K0 →+* ℝ) : ContinuousAdd (EmbeddedPoint σ) := by
  apply addition_of_injective_orbit (embedded σ (paperGenerator sqrt2_sq))
  · intro a b h
    change a • embedded σ (paperGenerator sqrt2_sq)=b • embedded σ (paperGenerator sqrt2_sq) at h
    rw [←embedded_multiple,←embedded_multiple] at h
    exact multiple_injective (embedded_injective σ h)
  · exact fun ne => off_diagonal _ ne

theorem continuous_add_pair : ContinuousAdd RealPair := by
  let _ := continuous_add_factor (place false)
  let _ := continuous_add_factor (place true)
  infer_instance

theorem topological_pair : IsTopologicalAddGroup RealPair :=
  { toContinuousAdd := continuous_add_pair, toContinuousNeg := continuous_neg_pair }

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.addition_of_injective_orbit
#print axioms Sun28.RealCharts.continuous_add_factor
#print axioms Sun28.RealCharts.continuous_add_pair
#print axioms Sun28.RealCharts.topological_pair
