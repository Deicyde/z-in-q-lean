import ScalarCoordinates

/-! Multiplication on the short formal group at a prime with e ≤ 3.
The first nonlinear term has order at least 5k at a point of depth k. -/
namespace Sun28.ScalarPlaces
open ZInQ ZInQ.Mult ZInQ.Assembly WeierstrassCurve.Affine
noncomputable section

theorem parameter_order_multiple {K : Type*} [Field K] [DecidableEq K]
    (v : AddValuation K (WithTop ℤ)) {A : K} (hA : 0≤v A)
    {p : ℕ} [Fact p.Prime] {e : ℤ} (ep : 1≤e) (small : e≤3) (hp : v (p:K)=(e:WithTop ℤ))
    (res : ∀ m : ℤ, ¬(p:ℤ)∣m → v (m:K)=0)
    {k : ℤ} {Q : (shortCurve A).toAffine.Point} (mem : Q∈W1 v A)
    (depth : v (zCoord Q)=(k:WithTop ℤ)) {m : ℤ} (nz : m≠0) :
    v (zCoord (m • Q))=((k+e*padicValInt p m:ℤ):WithTop ℤ) := by
  induction h : m.natAbs using Nat.strong_induction_on generalizing m k Q with
  | _ N ih =>
    have hk : 1≤k := by
      have d := one_le_val_zCoord hA mem
      rw [depth] at d
      exact_mod_cast d
    by_cases divides : (p:ℤ)∣m
    · obtain ⟨s,rfl⟩ := divides
      have sn : s≠0 := by rintro rfl; simp at nz
      have pn : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have lt : s.natAbs<N := by
        rw [←h,Int.natAbs_mul,Int.natAbs_natCast]
        have := (Fact.out : p.Prime).one_lt
        have := Int.natAbs_pos.mpr sn
        nlinarith
      have step := (zCoord_zsmul_eq_mul_unit_of_val hA mem depth (n:=(p:ℤ)) (c:=e)
        (by rw [Int.cast_natCast]; exact hp) (by omega)).1
      have inGroup : (p:ℤ) • Q∈W1 v A :=
        ((formalNbhd A hA).zsmul_mem ((mem_formalNbhd_iff hA Q).mpr mem) _).1
      have next := ih _ lt inGroup step sn rfl
      rw [mul_comm (p:ℤ) s,mul_smul,padicValInt.mul sn pn,padicValInt_self,next]
      exact WithTop.coe_eq_coe.mpr (by push_cast; ring)
    · have step := (zCoord_zsmul_eq_mul_unit_of_val hA mem depth (n:=m) (c:=0)
        (res m divides) (by omega)).1
      simpa only [padicValInt.eq_zero_of_not_dvd divides,Nat.cast_zero,mul_zero,add_zero] using step

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.parameter_order_multiple
