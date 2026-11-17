import LeadingOrders
import RegularSextic
/-! A unit chart for the primitive numerator and denominator of the rational input. -/
namespace ZInQBlueprint.PrimitiveParameters
open Polynomial IsDiscreteValuationRing ZInQBlueprint.IntegralSextic ZInQBlueprint.LeadingOrders
open ZInQBlueprint.RationalClusters ZInQBlueprint.PadicParameters ZInQBlueprint.ResidualFactors
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]
abbrev left (u : ℚ) := m (u.num : Zp) (u.den : Zp)
abbrev right (u : ℚ) := n (u.num : Zp) (u.den : Zp)

private theorem primeField (n : ℕ) (hn : 0<n) (hp : n<p) : (n:ZMod p)≠0 := by
  rw [Ne,CharP.cast_eq_zero_iff (ZMod p) p]; exact Nat.not_dvd_of_pos_of_lt hn hp
private theorem unit_iff (a : Zp) : IsUnit a ↔ PadicInt.toZMod a ≠ 0 := by
  rw [Ne,← RingHom.mem_ker,PadicInt.ker_toZMod,IsLocalRing.mem_maximalIdeal]; simp

theorem unit_nat (k : ℕ) (hk : 0<k) (hp : k<p) : IsUnit (k:Zp) := by
  apply (unit_iff p _).mpr
  rw [map_natCast]
  exact primeField p k hk hp

private theorem units (hp : 7≤p) : IsUnit (30:Zp) ∧ IsUnit (27:Zp) ∧ IsUnit (8:Zp) := by
  have h2 : IsUnit (2:Zp) := unit_nat p 2 (by decide) (by omega)
  have h3 : IsUnit (3:Zp) := unit_nat p 3 (by decide) (by omega)
  have h5 : IsUnit (5:Zp) := unit_nat p 5 (by decide) (by omega)
  rw [show (30:Zp)=2*3*5 by norm_num,show (27:Zp)=3^3 by norm_num,show (8:Zp)=2^3 by norm_num]
  exact ⟨(h2.mul h3).mul h5,h3.pow 3,h2.pow 3⟩

/-- Either use (x,z), or use the reciprocal chart (6z,x). -/
inductive Coordinates (u : ℚ) (t v a : Zp) : Prop where
  | first (hv : v=1) (ha : a=left p u) (ht : a*t=right p u)
  | second (hv : v=8) (ha : a=right p u) (ht : a*t=27*left p u)

theorem projective_chart {u : ℚ} {t v a : Zp} (H : Coordinates p u t v a) (δ : Zp) :
    (∀ x z, integralEquation δ (u.num:Zp) (u.den:Zp) x z = -6*δ*G p u*v*a^2*form 1 t x z) ∨
    (∀ x z, integralEquation δ (u.num:Zp) (u.den:Zp) (6*z) x = -6*δ*G p u*v*a^2*form 1 t x z) := by
  cases H with
  | first hv ha ht =>
    subst v; subst a
    left; intro x z
    change -6*δ*G p u*form (left p u) (right p u) x z=_
    rw [←ht,affine]; ring
  | second hv ha ht =>
    subst v; subst a
    right; intro x z
    change -6*δ*G p u*form (left p u) (right p u) (6*z) x=_
    rw [reciprocal_chart ht.symm]; ring

private theorem product_val (hp : 7≤p) (u : ℚ) :
    addVal Zp (left p u) + addVal Zp (right p u)=addVal Zp (F p u) := by
  have h : left p u * right p u=30*F p u := (parameter_identities _ _).1
  rw [← AddValuation.map_mul,h,AddValuation.map_mul,addVal_eq_zero_iff.mpr (units p hp).1,zero_add]
theorem positive_parameter (u : ℚ) (hp : 7≤p) (s : ℕ) (hs : 0<s)
    (hf : addVal Zp (F p u)=(s:ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧ addVal Zp t=(s:ℕ∞) := by
  let : NeZero (2:ZMod p) := ⟨primeField p 2 (by decide) (by omega)⟩
  let : NeZero (3:ZMod p) := ⟨primeField p 3 (by decide) (by omega)⟩
  let : NeZero (5:ZMod p) := ⟨primeField p 5 (by decide) (by omega)⟩
  have hF : PadicInt.toZMod (F p u)=0 := by
    by_contra h
    have hzero := addVal_eq_zero_iff.mpr ((unit_iff p _).mpr h)
    rw [hf] at hzero
    exact hs.ne' (by exact_mod_cast hzero)
  have hF' : contactProduct (PadicInt.toZMod (u.num:Zp)) (PadicInt.toZMod (u.den:Zp))=0 := by
    simpa only [F,contactProduct,map_mul,map_add,map_ofNat] using hF
  have hab := (rational_primitive (p:=p) u).imp (unit_iff p _).mp (unit_iff p _).mp
  have hG : IsUnit (G p u) := (unit_iff p _).mpr (by
    simpa only [G,poleForm,map_mul,map_pow,map_add,map_ofNat] using ClusterParameters.separate_marks hab hF')
  have hpv := (product_val p hp u).trans hf
  obtain ha | hb := chart_exists _ _ hG
  · change IsUnit (left p u) at ha
    let a := ha.unit
    let t := (↑a⁻¹:Zp)*right p u
    refine ⟨t,1,a,.first (by simp) ha.unit_spec (by simp [t]),?_⟩
    change addVal Zp ((↑a⁻¹:Zp)*right p u)=_
    rw [AddValuation.map_mul,addVal_eq_zero_iff.mpr (a⁻¹).isUnit,zero_add]
    simpa only [addVal_eq_zero_iff.mpr ha,zero_add] using hpv
  · change IsUnit (right p u) at hb
    let a := hb.unit
    let t := (↑a⁻¹:Zp)*(27*left p u)
    obtain ⟨_,h27,h8⟩ := units p hp
    refine ⟨t,h8.unit,a,.second h8.unit_spec hb.unit_spec (by simp [t]),?_⟩
    change addVal Zp ((↑a⁻¹:Zp)*(27*left p u))=_
    rw [AddValuation.map_mul,AddValuation.map_mul,addVal_eq_zero_iff.mpr (a⁻¹).isUnit,
      addVal_eq_zero_iff.mpr h27,zero_add,zero_add]
    simpa only [addVal_eq_zero_iff.mpr hb,add_zero] using hpv

theorem even_parameter (u : ℚ) (hp : 17≤p) (k : ℕ) (hk : 0<k)
    (hf : addVal Zp (F p u)=((2*k:ℕ):ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧ addVal Zp t=((2*k:ℕ):ℕ∞) :=
  positive_parameter p u (by omega) (2*k) (by omega) hf

/-- A pole lies in the first chart. Its parameter satisfies the univariate discriminant equation. -/
theorem pole_parameter (u : ℚ) (hp : 17≤p) (g : ℕ) (hg : 0<g)
    (hG : addVal Zp (G p u)=(g:ℕ∞)) :
    ∃ t : Zpˣ, ∃ a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      (a:Zp)^2*((t:Zp)^2+27)=(G p u)^3 := by
  obtain ⟨_,hF,_⟩ := pole_data (by omega) _ _ (rational_primitive u) g hg hG
  have h : IsUnit (left p u*right p u) := by
    rw [show left p u*right p u=30*F p u from (parameter_identities _ _).1]
    exact (units p (by omega)).1.mul hF
  have ha := isUnit_of_mul_isUnit_left h
  have hb := isUnit_of_mul_isUnit_right h
  let a := ha.unit
  let t := a⁻¹*hb.unit
  have ht : (a:Zp)*(t:Zp)=right p u := by simp [t]
  refine ⟨t,a,.first rfl ha.unit_spec ht,?_⟩
  have hh : (G p u)^3=27*(left p u)^2+(right p u)^2 := (parameter_identities _ _).2.1
  rw [←ht,←ha.unit_spec] at hh
  linear_combination -hh
/-- On the complement of the contact and pole divisors the actual reduced polynomial is separable. -/
theorem ordinary_parameter (u : ℚ) (hp : 7≤p) (hF : IsUnit (F p u)) (hG : IsUnit (G p u)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      (ZInQBlueprint.DirectCharts.monicSextic (IsLocalRing.residue Zp (t:Zp))).Separable := by
  have h : IsUnit (left p u*right p u) := by
    rw [show left p u*right p u=30*F p u from (parameter_identities _ _).1]
    exact (units p hp).1.mul hF
  let a := (isUnit_of_mul_isUnit_left h).unit
  let b := (isUnit_of_mul_isUnit_right h).unit
  let t := a⁻¹*b
  have ha : (a:Zp)=left p u := IsUnit.unit_spec _
  have hb : (b:Zp)=right p u := IsUnit.unit_spec _
  have ht : (a:Zp)*(t:Zp)=right p u := by simp [t,hb]
  have h2 : IsUnit (2:Zp) := unit_nat p 2 (by decide) (by omega)
  let : NeZero (2:IsLocalRing.ResidueField Zp) :=
    ⟨by simpa only [map_ofNat] using (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h2⟩
  have he : (a:Zp)^2*((t:Zp)^2+27)=(G p u)^3 := by
    have hh : (G p u)^3=27*(left p u)^2+(right p u)^2 := (parameter_identities _ _).2.1
    rw [←ht,←ha] at hh
    linear_combination -hh
  refine ⟨t,a,.first rfl ha ht,ZInQBlueprint.RegularSextic.separable ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr t.isUnit) ?_⟩
  intro hz
  have he' := congrArg (IsLocalRing.residue Zp) he
  simp only [map_mul,map_add,map_pow,map_ofNat,hz,mul_zero] at he'
  exact pow_ne_zero 3 ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hG) he'.symm

end
end ZInQBlueprint.PrimitiveParameters
#print axioms ZInQBlueprint.PrimitiveParameters.projective_chart
#print axioms ZInQBlueprint.PrimitiveParameters.even_parameter
#print axioms ZInQBlueprint.PrimitiveParameters.pole_parameter
#print axioms ZInQBlueprint.PrimitiveParameters.ordinary_parameter
#print axioms ZInQBlueprint.PrimitiveParameters.positive_parameter
#print axioms ZInQBlueprint.PrimitiveParameters.unit_nat
