import PaperAnchor

/-! The incomplete elliptic logarithm is an isometry on each fixed formal neighbourhood. -/
namespace Sun28.OrdinaryIntegrality
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.Ordinary Sun28.FixedPreparation
noncomputable section

private def term (b z : K0) (j : ℕ) : K0 :=
  ((2*(j+1)).choose (j+1):K0)*b^(j+1)*z^(4*(j+1))/(4*(j+1)+1:ℕ)

private theorem expansion (b z : K0) :
    logTrunc (shortDifferential b) 64 z=z*(1+∑ j∈Finset.range 15,term b z j) := by
  simp only [logTrunc,shortDifferential,term,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num
  ring

theorem denominators {q j : ℕ} [hp : Fact q.Prime] (small : q≤23) (hj : j<15)
    {π : Zs} (prime : Prime π) (above : π∣(q:Zs)) :
    ∃ a : ℤ, a≤2 ∧ vP π prime ((4*(j+1)+1:ℕ):K0)=(a:WithTop ℤ) := by
  let n:=4*(j+1)+1
  have nz : n≠0 := by dsimp [n]; omega
  have kn : (n:K0)≠0 := Nat.cast_ne_zero.mpr nz
  rw [show 4*(j+1)+1=n from rfl,vP_apply prime kn]
  by_cases even : q=2
  · have odd : ¬q∣n := by rw [even]; dsimp [n]; omega
    exact ⟨0,by decide,by rw [vp_natCast_of_not_dvd prime above odd]⟩
  · have audit : ∀ p:Fin 24,∀ i:Fin 15,p.val.Prime → ¬p.val^3∣4*(i.val+1)+1 := by decide
    have no := audit ⟨q,by omega⟩ ⟨j,hj⟩ hp.out
    have bound : padicValNat q n≤2 := by
      by_contra! high
      exact no ((padicValNat_dvd_iff_le nz).mpr high)
    exact ⟨padicValNat q n,by exact_mod_cast bound,by rw [vp_natCast even prime above nz]⟩

theorem log64_order {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs} (prime : Prime π)
    (above : π∣(q:Zs)) {b z : K0} (bi : Vge (vP π prime) 0 b) (deep : Vge (vP π prime) 1 z) :
    vP π prime (logTrunc (shortDifferential b) 64 z)=vP π prime z := by
  let v:=vP π prime
  have summand (j : ℕ) (hj : j∈Finset.range 15) : Vge v 1 (term b z j) := by
    obtain ⟨a,ha,ord⟩:=denominators small (Finset.mem_range.mp hj) prime above
    have bnd:=((vge_natCast (v:=v) ((2*(j+1)).choose (j+1))).mul (bi.pow (j+1))).mul (deep.pow (4*(j+1)))
    exact (bnd.div_val' ord).mono (by push_cast; omega)
  rw [expansion,(vP π prime).map_mul,val_one_add (Vge.sum_of_le summand),add_zero]

private theorem z_eq (b : K0) (Q : (curve b).Point) : parameter Q=zCoord Q := by cases Q <;> rfl

theorem multiple_integral {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs} (prime : Prime π)
    (above : π∣(q:Zs)) {b : K0} (bi : Vge (vP π prime) 0 b) {Q : (curve b).Point}
    (near : Q∈W1 (vP π prime) b) (n : ℤ) :
    Vge (vP π prime) 0 (reciprocal (n • Q)) ∧
    Vge (vP π prime) 0 (logTrunc (shortDifferential b) 64 (parameter (n • Q)) /
      logTrunc (shortDifferential b) 64 (parameter Q)) := by
  let v:=vP π prime
  obtain ⟨mem,mon⟩:=zsmul_mem_W1 bi near n
  have par (Y : (curve b).Point) (hY : Y∈W1 v b) :
      v (logTrunc (shortDifferential b) 64 (parameter Y))=v (zCoord Y) := by
    rw [z_eq]; exact log64_order small prime above bi (one_le_val_zCoord bi hY)
  have recip (Y : (curve b).Point) (form : Y∈W1 v b) : Vge v 0 (reciprocal Y) := by
    cases Y with
    | zero => exact Vge.zero _
    | some x y hw =>
      obtain ⟨N,pos,_,_,_,_,rc,_⟩:=formal_val_x_y bi hw form
      change Vge v 0 x⁻¹
      change v (1/x)=((2*N:ℤ):WithTop ℤ) at rc
      rw [one_div] at rc
      exact (Vge.of_eq rc).mono (by omega)
  constructor
  · exact recip _ mem
  · by_cases zero : logTrunc (shortDifferential b) 64 (parameter Q)=0
    · rw [zero,div_zero]; exact Vge.zero _
    · obtain ⟨m,hm⟩:=val_eq_coe (v:=v) zero
      have hm' := (par Q near).symm.trans hm
      have num : Vge v m (logTrunc (shortDifferential b) 64 (parameter (n • Q))) := by
        exact hm'.ge.trans (mon.trans_eq (par (n • Q) mem).symm)
      exact (num.div_val' hm).mono (by omega)

end
#print axioms denominators
#print axioms log64_order
#print axioms multiple_integral
end Sun28.OrdinaryIntegrality
