import ScalarModel
import ScalarMultiples

/-! Orders of the scalar readouts at an odd prime and at the unique prime above 2. -/
namespace Sun28.ScalarPlaces
open ZInQ ZInQ.Mult ZInQ.Size ZInQ.Assembly ZInQ.Syntax Sun28.Scalar Sun28.WitnessIndices
noncomputable section
abbrev formalZ (Q : genCurve.toAffine.Point) := zCoord (A:= -genD^2) Q
abbrev scalarRec (n : ℤ) := reciprocal (scalarEquiv (n • P))
abbrev scalarParam (n : ℤ) := parameter (scalarEquiv (n • P))

theorem scaled_orders {π : Zs} (hπ : Prime π) (n : ℤ) :
    vP π hπ (scalarRec n)=vP π hπ (xi (n • genP0)) ∧
    vP π hπ (scalarParam n)=vP π hπ (formalZ (n • genP0)) := by
  obtain ⟨x,z⟩ := scaled_multiple n
  simp only [scalarRec,scalarParam,x,z,(vP π hπ).map_div,(vP π hπ).map_pow,
    unit_epsilon hπ,nsmul_zero,sub_zero,formalZ,and_self]

private theorem pair_at (π : Zs) (hπ : Prime π) {κ : ℕ}
    (positive : 0<κ) {p : ℕ} [Fact p.Prime] {e : ℤ} (ep : 1≤e) (small : e≤3)
    (hp : vP π hπ (p:K0)=(e:WithTop ℤ))
    (res : ∀ m : ℤ, ¬(p:ℤ)∣m → vP π hπ (m:K0)=0)
    (inGroup : (κ:ℤ) • genP0∈W1 (vP π hπ) (-genD^2))
    {h c : ℤ} (hn : h≠0) (cn : c≠0) (dh : (κ:ℤ)∣h) (dc : (κ:ℤ)∣c) :
    ∃ k : ℤ, 1≤k ∧
      (let depth (n : ℤ) := k+e*((padicValInt p n:ℤ)-padicValNat p κ)
       ((2*depth h:ℤ):WithTop ℤ)≤vP π hπ (scalarRec h) ∧
       ((2*depth c:ℤ):WithTop ℤ)≤vP π hπ (scalarRec c) ∧
       vP π hπ (scalarParam c/scalarParam h)=((e*((padicValInt p c:ℤ)-padicValInt p h):ℤ):WithTop ℤ)) := by
  let v:=vP π hπ
  let hA:=vP_genA_nonneg π hπ
  have κn : (κ:ℤ)≠0 := by exact_mod_cast positive.ne'
  have nz : (κ:ℤ) • genP0≠0 := fun eb => κn (zsmul_genP0_injective (eb.trans (zero_zsmul genP0).symm))
  obtain ⟨k,high,hk⟩ := val_zCoord_of_mem_W1 hA inGroup nz
  have atIndex (n : ℤ) (nn : n≠0) (dn : (κ:ℤ)∣n) :
      let depth := k+e*((padicValInt p n:ℤ)-padicValNat p κ)
      ((2*depth:ℤ):WithTop ℤ)≤v (scalarRec n) ∧ v (scalarParam n)=(depth:WithTop ℤ) := by
    obtain ⟨s,hs⟩ := dn
    have sn : s≠0 := by rintro rfl; simp [hs] at nn
    have smul : n • genP0=s • ((κ:ℤ) • genP0) := by rw [hs,mul_comm,mul_smul]
    have equality : (padicValInt p n:ℤ)-padicValNat p κ=padicValInt p s := by
      rw [hs,padicValInt.mul κn sn]
      simp [padicValInt]
    have order := parameter_order_multiple v hA ep small hp res inGroup hk sn
    have mem : n • genP0∈W1 v (-genD^2) := by
      rw [smul]
      exact ((formalNbhd _ hA).zsmul_mem ((mem_formalNbhd_iff hA _).mpr inGroup) s).1
    dsimp only
    rw [equality,(scaled_orders hπ n).1,(scaled_orders hπ n).2]
    have ordn : v (formalZ (n • genP0))=((k+e*padicValInt p s:ℤ):WithTop ℤ) := by rw [smul]; exact order
    exact ⟨vP_xi_ge hπ (Q:=n • genP0) ⟨mem,ordn.ge⟩,ordn⟩
  obtain ⟨hh,zh⟩ := atIndex h hn dh
  obtain ⟨cc,zc⟩ := atIndex c cn dc
  refine ⟨k,high,hh,cc,?_⟩
  rw [val_div_coe zc zh]
  exact WithTop.coe_eq_coe.mpr (by ring)

/-- At odd primes the finite reduction order supplies the entry into the formal group. -/
theorem odd_pair {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) (π : Zs) (hπ : Prime π)
    (above : π∣(p:Zs)) {κ : ℕ} (positive : 0<κ) (multiple : orderAbove p∣κ)
    {h c : ℤ} (hn : h≠0) (cn : c≠0) (dh : (κ:ℤ)∣h) (dc : (κ:ℤ)∣c) :
    ∃ k : ℤ, 1≤k ∧
      (let depth (n : ℤ) := k+((padicValInt p n:ℤ)-padicValNat p κ)
       ((2*depth h:ℤ):WithTop ℤ)≤vP π hπ (scalarRec h) ∧
       ((2*depth c:ℤ):WithTop ℤ)≤vP π hπ (scalarRec c) ∧
       vP π hπ (scalarParam c/scalarParam h)=((((padicValInt p c:ℤ)-padicValInt p h):ℤ):WithTop ℤ)) := by
  obtain ⟨t,eq⟩ := multiple
  have inGroup := (orderAbove_spec hp.out odd).2.2 π hπ above (t:ℤ)
  have cast : (t:ℤ)*orderAbove p=κ := by rw [eq]; push_cast; ring
  rw [cast,E1sub_eq_formalNbhd] at inGroup
  simpa only [one_mul] using pair_at π hπ positive (e:=1) (by decide) (by decide)
    (vP_natCast_self odd hπ above) (vP_intCast_of_not_dvd odd hπ above) inGroup.1 hn cn dh dc

theorem dyadic_pair {κ : ℕ} (positive : 0<κ) {h c : ℤ} (hn : h≠0) (cn : c≠0)
    (dh : (κ:ℤ)∣h) (dc : (κ:ℤ)∣c) :
    ∃ k : ℤ, 1≤k ∧
      (let depth (n : ℤ) := k+2*((padicValInt 2 n:ℤ)-padicValNat 2 κ)
       ((2*depth h:ℤ):WithTop ℤ)≤vS (scalarRec h) ∧
       ((2*depth c:ℤ):WithTop ℤ)≤vS (scalarRec c) ∧
       vS (scalarParam c/scalarParam h)=((2*((padicValInt 2 c:ℤ)-padicValInt 2 h):ℤ):WithTop ℤ)) :=
  pair_at sqrt2Z prime_sqrt2Z positive (e:=2) (by decide) (by decide) vS_two_eq
    vS_intCast_of_not_dvd (zsmul_genP0_mem_formal κ).1 hn cn dh dc

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.scaled_orders
#print axioms Sun28.ScalarPlaces.odd_pair
#print axioms Sun28.ScalarPlaces.dyadic_pair
