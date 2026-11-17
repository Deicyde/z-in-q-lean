import SelectedIntegralPlace
import SelectedShifts
import ZInQKernel.Multiplication.Completeness.SlopeCompleteness

/-! The two actual finite-group orders imply both formal anchors for
Sun's curve. No separately supplied number-field prime remains. -/
namespace Sun28.SelectedTrace
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.ContactFactors NumberField IsDedekindDomain
open WeierstrassCurve WeierstrassCurve.Affine
open scoped NumberField
noncomputable section

private theorem three_sub_nonzero {p : ℕ} [pp : Fact p.Prime] (large : 65<p)
    {r : ZMod p} (hr : r^2=2) : 3-r≠0 := by
  intro e
  have same : r=3 := (sub_eq_zero.mp e).symm
  rw [same] at hr
  have seven : (7:ZMod p)=0 := by linear_combination hr
  have divides := (ZMod.natCast_eq_zero_iff 7 p).mp seven
  have := Nat.le_of_dvd (by decide : 0<7) divides
  omega

/-- Multiplication by a multiple of the group order reduces to the identity
on the short curve with the coefficient actually printed by Sun. -/
theorem anchor_from_order {p : ℕ} [pp : Fact p.Prime] (large : 65<p)
    {r : ZMod p} (hr : r^2=2) {π : Zs} (hπ : Prime π)
    (kernel : ∀ a, residueAt r hr a=0 ↔ π∣a) {h : ℤ}
    (order : (pointCount p (-(3-r)^2):ℤ)∣h) :
    h • paperGenerator sqrt2_sq ∈ W1 (vP π hπ) (-(3-sqrt2)^2) := by
  let b : K0 := -(3-sqrt2)^2
  let B : Zs := -(3-sqrt2Z)^2
  let ρ := residueAt r hr
  have lift : Zs.toK0 B=b := by simp [B,b,map_ofNat]
  have bInt : VGe π 0 b := by
    rw [←lift]; exact Or.inr (vp_nonneg hπ B)
  have bRes : res π ρ b= -(3-r)^2 := by
    rw [←lift,res_toK0 hπ ρ kernel]
    simp only [B,map_neg,map_pow,map_sub,map_ofNat]
    have root : ρ sqrt2Z=r := by simp [ρ,sqrt2Z]
    rw [root]
  have three : (3-sqrt2:K0)≠0 := by
    intro e
    have same : sqrt2=3 := (sub_eq_zero.mp e).symm
    have two:=sqrt2_sq
    rw [same] at two
    norm_num at two
  let _ : (shortCurve b).IsElliptic := shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ three))
  let _ : NeZero (2:ZMod p) := ⟨two_ne_zero_zmod (by omega)⟩
  let _ : (shortCurve (-(3-r)^2)).IsElliptic :=
    shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ (three_sub_nonzero large hr)))
  let P : (shortCurve b).toAffine.Point:=paperGenerator sqrt2_sq
  have redZero : red hπ ρ kernel bInt bRes (h • P)=0 := by
    obtain ⟨k,rfl⟩ := order
    rw [← redHom_apply,map_zsmul,mul_comm ((pointCount p (-(3-r)^2):ℕ):ℤ) k,←smul_smul,
      natCast_zsmul,← card_point_shortCurve p,card_nsmul_eq_zero',smul_zero]
  change h • P ∈ W1 (vP π hπ) b
  generalize h • P=Z at redZero ⊢
  cases Z with
  | zero => exact trivial
  | some x y he =>
    by_cases integral : VGe π 0 x
    · rw [red_some_of_vge hπ ρ kernel bInt bRes he integral] at redZero
      exact False.elim ((Point.some_ne_zero _) redZero)
    · have xn : x≠0 := fun e => integral (Or.inl e)
      change vP π hπ x<0
      rw [vP_apply hπ xn]
      exact WithTop.coe_lt_coe.mpr (lt_of_not_ge ((vge_iff xn).not.mp integral))

/-- The two split reduced-group orders suffice for the trace and pole valuations
over each selected prime. The root r fixes their orientation. -/
theorem selected_shift_pole_of_counts {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (vp : 0<v) {j : Fin 3} (nz : A j≠0) {p : ℕ} [pp : Fact p.Prime]
    (sel : p∈selected values j) (large : 65<p) (off : ¬p∣dilation A) (good : ¬p∣separation)
    (unit : padicValRat p (A j)=0) {r : ZMod p} (hr : r^2=2)
    {points : NinePoints} {M : ℕ} {c q h : ℤ} {n : Fin 4→ℤ}
    (represented : Consequences points M c ⟨q,h,n,fun i=>h*n i⟩)
    (β : ℚ) (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : β=(n 0:ℚ))
    (firstOrder : (pointCount p (-(3-r)^2):ℤ)∣h)
    (secondOrder : (pointCount p (-(3+r)^2):ℤ)∣(h-c)) :
    let t:=argument A u v j
    let T:=ordinaryTraceAt points M c β (A j) t
    T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  obtain ⟨π,hπ,kernel⟩ := exists_prime_residueAt r hr
  have hr' : (-r)^2=2 := by rwa [neg_sq]
  have kernel' := residueAt_neg_ker hr kernel hr'
  have dvd := (kernel (p:Zs)).mp (by simp)
  let _ := selectedPlace_liesOver hπ dvd
  apply selected_shift_pole values one vp nz sel large off good unit (selectedPlace π hπ)
    represented β root firstRoot
  · rw [selectedPlace_order]; exact anchor_from_order large hr hπ kernel firstOrder
  · rw [selectedPlace_conjugate_order]; exact anchor_from_order large hr' (prime_star hπ) kernel' (by simpa using secondOrder)

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.anchor_from_order
#print axioms Sun28.SelectedTrace.selected_shift_pole_of_counts
