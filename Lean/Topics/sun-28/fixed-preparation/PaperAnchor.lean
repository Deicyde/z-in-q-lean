import OddAnchor

/-! Membership, including the formal-neighbourhood condition, on the displayed Sun curve. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace Sun28.FixedPreparation
open WeierstrassCurve.Affine ZInQ ZInQ.Mult ZInQ.Assembly Sun28.Scalar Sun28.Ordinary
noncomputable section
attribute [local irreducible] anchor

private def nearAny {C : WeierstrassCurve.Affine K0} (v : AddValuation K0 (WithTop ℤ)) :
    C.Point → Prop
  | .zero => True
  | .some x _ _ => v x < 0

private theorem transfer_neighbourhood {π : Zs} (hπ : Prime π) (m : ℤ)
    (near : m • genP0 ∈ W1 (vP π hπ) (-genD^2)) :
    m • paperGenerator sqrt2_sq ∈ W1 (vP π hπ) (-(3-sqrt2)^2) := by
  let v := vP π hπ
  have changeModel {C D : WeierstrassCurve.Affine K0} (e : C=D) (p : C.Point) (q : D.Point)
      (he : HEq p q) : nearAny v (m • p) ↔ nearAny v (m • q) := by
    subst D; rw [eq_of_heq he]
  have criterion (b : K0) (p : (curve b).Point) : p ∈ W1 v b ↔ nearAny v p := by cases p <;> rfl
  rw [criterion,changeModel generator_cast.1 _ _ generator_cast.2,
    show curveGenerator=theta genP0 from theta_genP0.symm,←map_zsmul]
  cases eq : m • genP0 with
  | zero => trivial
  | some x y h =>
    have neg : v x<0 := by rw [eq] at near; exact near
    rw [theta_some]
    change v (epsilon^4*x)<0
    have eu : v epsilon=0 := by
      change vP π hπ epsilon=0
      rw [vP_apply hπ epsilon_ne_zero,←toK0_epsUnit,vp_unit hπ]; rfl
    simpa only [v.map_mul,v.map_pow,eu,nsmul_zero,zero_add] using neg

theorem paper_integral {π : Zs} (hπ : Prime π) : 0≤vP π hπ (-(3-sqrt2)^2) := by
  rw [←delta_eq,show -delta^2=Zs.toK0 (-deltaZ^2) by simp]
  exact vP_toK0_nonneg _ _

private theorem parameter_eq_coord (b : K0) (p : (curve b).Point) :
    parameter p=zCoord (A:=b) p := by cases p <;> rfl

/-- All local preparation conditions on the actual paper point. The order convention gives
four uniformizer layers at the ramified prime, and two at all the other primes. -/
theorem fixed_anchor_prepared {q : ℕ} [Fact q.Prime] (small : q≤23)
    {π : Zs} (hπ : Prime π) (above : π∣(q:Zs)) :
    anchor • paperGenerator sqrt2_sq ∈ formalFilt (-(3-sqrt2)^2) (paper_integral hπ)
      (if q=2 then 4 else 2) := by
  by_cases even : q=2
  · subst q
    have sq : π∣sqrt2Z^2 := by simpa only [Nat.cast_ofNat,←two_eq_sqrt2Z_sq] using above
    have ass := hπ.associated_of_dvd prime_sqrt2Z (hπ.dvd_of_dvd_pow sq)
    have all := (mem_Ek_iff prime_sqrt2Z 3 (anchor • genP0)).mpr (zsmul_genP0_mem_formal anchor)
    have n : anchor • genP0 ∈ Ek π hπ 3 := (Ek_congr hπ prime_sqrt2Z ass 3 (anchor • genP0)).mpr all
    apply (mem_formalFilt_iff (paper_integral hπ) 4 (anchor • paperGenerator sqrt2_sq)).mpr
    refine ⟨transfer_neighbourhood hπ anchor ((mem_Ek_iff hπ 3 (anchor • genP0)).mp n).1,?_⟩
    rw [←parameter_eq_coord,vP_congr hπ prime_sqrt2Z ass]
    exact anchor_dyadic
  · simp only [even, ↓reduceIte]
    apply (mem_formalFilt_iff (paper_integral hπ) 2 (anchor • paperGenerator sqrt2_sq)).mpr
    refine ⟨transfer_neighbourhood hπ anchor ((mem_Ek_iff hπ 2 (anchor • genP0)).mp (anchor_odd even small hπ above)).1,?_⟩
    rw [←parameter_eq_coord]
    exact paper_anchor_odd even small hπ above

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.paper_integral
#print axioms Sun28.FixedPreparation.fixed_anchor_prepared
