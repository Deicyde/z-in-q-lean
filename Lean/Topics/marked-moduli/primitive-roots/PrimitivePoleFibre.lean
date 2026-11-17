import PrimitivePole
import PrimitiveRoots
namespace ZInQBlueprint.PrimitivePoleFibre
open Polynomial IsLocalRing IsDiscreteValuationRing
open ZInQBlueprint.PrimitivePole ZInQBlueprint.PrimitiveLifts ZInQBlueprint.DirectCharts
open ZInQBlueprint.IntegralSextic ZInQBlueprint.ResidueExtension ZInQBlueprint.ClusterRoots
noncomputable section
variable {R : Type*} [CommRing R]
private def divided (a e c U : R) : R[X] := poleDivided (C a) (C e) (C c) (C U) X
private theorem eval_divided (a e c U x : R) :
    (divided a e c U).eval x = poleDivided a e c U x := by
  simp [divided,poleDivided,DirectCharts.slope,variation,alpha,beta,gamma]
private theorem map_divided {S : Type*} [CommRing S] (φ : R →+* S) (a e c U : R) :
    (divided a e c U).map φ = divided (φ a) (φ e) (φ c) (φ U) := by
  simp [divided,poleDivided,DirectCharts.slope,variation,alpha,beta,gamma]
private theorem reduced_divided (a e U : R) :
    divided a e 0 U = C ((slope e a)^3)*X^3+C (U*variation e a) := by
  change poleDivided (C a) (C e) (C 0) (C U) X = _
  simpa [DirectCharts.slope,variation,alpha,beta,gamma,map_ofNat] using pole_reduction (C a) (C e) (C U) X
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "κ" => ResidueField W
private instance henselian : HenselianRing W (IsLocalRing.maximalIdeal W) := by
  rw [ResidueExtension.maximalIdeal_eq]; infer_instance

theorem pole_scaled (hp : 7≤p) (k : ℕ) (hk : 0<k) (e U H V : W) (he : e^2= -3)
    (hH : IsUnit H) (hV : IsUnit V)
    (hU : (residue W V)^3= -96*residue W e*(residue W H)^6*residue W U) :
    Nonempty (SexticFibre (monicSextic (-3*e+((p:W)^k)^3*U)) ((p:W)^k)) := by
  let c := (p:W)^k
  let ρ := residue W
  have h₂ : (2:κ) ≠ 0 := small_residue p 2 (by decide) (by omega)
  have h₃ : (3:κ) ≠ 0 := small_residue p 3 (by decide) (by omega)
  have h2 : IsUnit (2:W) := (residue_ne_zero_iff_isUnit _).mp (by simpa [map_ofNat] using h₂)
  have h3 : IsUnit (3:ℤ_[p]) := small_unit p 3 (by decide) (by omega)
  obtain ⟨d,hd0⟩ := padic_unit_square_root p (by omega) (3:ℤ_[p]) h3
  have hd : d^2=3 := by simpa only [map_ofNat] using hd0
  let inv : W := (h2.unit⁻¹ : Wˣ)
  have hi : 2*inv=1 := by simpa only [h2.unit_spec] using Units.mul_inv h2.unit
  let a : Fin 2 → W := ![centre e d inv,centre e (-d) inv]
  have h4W : (4:W) ≠ 0 := by convert pow_ne_zero 2 h2.ne_zero using 1; norm_num
  have ha (i) : q e (a i)=0 := by
    fin_cases i
    · exact centre_root he hd hi h4W
    · exact centre_root he (by simpa using hd : (-d)^2=3) hi h4W
  have he' : (ρ e)^2= -3 := by simpa [ρ,map_ofNat] using congrArg ρ he
  have hd' : (ρ d)^2=3 := by simpa [ρ,map_ofNat] using congrArg ρ hd
  have hd₀ : ρ d ≠ 0 := fun h => h₃ (by simpa [h] using hd'.symm)
  have he1 : ρ e ≠ 1 := by
    intro e1
    have h4 : (4:κ) ≠ 0 := small_residue p 4 (by decide) (by omega)
    apply h4
    rw [e1] at he'
    linear_combination he'
  have hn : ρ (centre e d inv) ≠ ρ (centre e (-d) inv) := by
    apply sub_ne_zero.mp
    rw [← map_sub,centre_difference hi,map_mul,map_sub,map_one]
    exact mul_ne_zero hd₀ (sub_ne_zero.mpr he1.symm)
  have hinj : Function.Injective (fun i => ρ (a i)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a,hn.symm]
  let g i := divided (a i) e c U
  let P i := C ((slope (ρ e) (ρ (a i)))^3)*X^3+C (ρ U*variation (ρ e) (ρ (a i)))
  obtain ⟨hc,hc₀⟩ := uniformizer_scale p k hk
  obtain ⟨hm,hdg⟩ := monic_six (-3*e+c^3*U)
  apply lift_rows (a:=a) hc hc₀ hinj hm.ne_zero hdg.le g P
  · intro i x
    rw [monic_eval,pole_divided he (ha i),eval_divided]
  · intro i
    change (divided _ _ _ _).map _ = _
    rw [map_divided,hc₀,reduced_divided]
  · intro i
    apply pole_rows h₂ h₃ he' (by simpa [q,map_ofNat] using congrArg ρ (ha i))
      ((residue_ne_zero_iff_isUnit _).mpr hH) ((residue_ne_zero_iff_isUnit _).mpr hV) hU

/-- Lift the sign of the pole already specified by the residue of t. -/
private theorem signed_centre (hp : 7≤p) (t : W) (ht : (residue W t)^2+27=0) :
    ∃ e : W, e^2= -3 ∧ residue W t= -3*residue W e := by
  let ρ := residue W
  have h₂ : (2:κ) ≠ 0 := small_residue p 2 (by decide) (by omega)
  have h₃ : (3:κ) ≠ 0 := small_residue p 3 (by decide) (by omega)
  let r := -(ρ t)/3
  have hr : r^2= -3 := by dsimp [r]; field_simp; linear_combination ht
  have hr₀ : r ≠ 0 := by
    intro h
    apply neg_ne_zero.mpr h₃
    simpa [h] using hr.symm
  let P : W[X] := X^2+C 3
  have hz : P.eval₂ ρ r=0 := by simp [P,ρ,map_ofNat,hr]
  have hs : P.derivative.eval₂ ρ r ≠ 0 := by
    simpa [P,ρ,derivative_pow,map_ofNat] using mul_ne_zero h₂ hr₀
  obtain ⟨e,he,hres⟩ := ZInQBlueprint.HenselTriples.liftSimple P r hz hs
  refine ⟨e,?_,?_⟩
  · change P.eval e=0 at he
    simp [P] at he
    linear_combination he
  · rw [hres]
    dsimp [r,ρ]; field_simp

theorem pole_identity (hp : 7≤p) (g : ℕ) (hg : 0<g) (t M H V : W)
    (hH : IsUnit H) (hV : IsUnit V) (hM : residue W M= -4*(residue W H)^3)
    (ht : M^2*(t^2+27)=((p:W)^g)^3*V^3) :
    Nonempty (SexticFibre (monicSextic t) ((p:W)^g)) := by
  let c := (p:W)^g
  let ρ := residue W
  obtain ⟨_,hc0⟩ := uniformizer_scale p g hg
  have h4 : (4:κ) ≠ 0 := small_residue p 4 (by decide) (by omega)
  have h3 : (3:κ) ≠ 0 := small_residue p 3 (by decide) (by omega)
  have h6 : (6:κ) ≠ 0 := small_residue p 6 (by decide) (by omega)
  have hM0 : ρ M ≠ 0 := by
    rw [show ρ M= -4*(ρ H)^3 from hM]
    exact mul_ne_zero (neg_ne_zero.mpr h4) (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr hH))
  have hred : (ρ t)^2+27=0 := by
    have h := congrArg ρ ht
    change ρ (M^2*(t^2+27))=ρ (c^3*V^3) at h
    simp only [map_mul,map_pow,map_add,map_ofNat] at h
    have hc : ρ c=0 := hc0
    rw [hc,zero_pow (by decide),zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hM0)
  obtain ⟨e,he,het⟩ := signed_centre p hp t hred
  have he0 : ρ e ≠ 0 := by
    have he' : (ρ e)^2= -3 := by simpa [ρ,map_ofNat] using congrArg ρ he
    intro h; exact neg_ne_zero.mpr h3 (by simpa [h] using he'.symm)
  let J := M^2*(t-3*e)
  have hJ : IsUnit J := by
    apply (residue_ne_zero_iff_isUnit _).mp
    change ρ (M^2*(t-3*e)) ≠ 0
    simp only [map_mul,map_pow,map_sub,map_ofNat]
    apply mul_ne_zero (pow_ne_zero _ hM0)
    rw [show ρ t= -3*ρ e from het,show -3*ρ e-3*ρ e= -6*ρ e by ring]
    exact mul_ne_zero (neg_ne_zero.mpr h6) he0
  let U := (hJ.unit⁻¹ : Wˣ).val*V^3
  have hJU : J*U=V^3 := by
    calc J*U = ((hJ.unit:W)*(↑(hJ.unit⁻¹):W))*V^3 := by rw [hJ.unit_spec]; ring
         _ = _ := by simp
  have scale : t= -3*e+c^3*U := by
    apply mul_left_cancel₀ hJ.ne_zero
    have h : J*(t+3*e)=c^3*V^3 := by
      dsimp [J,c]; linear_combination ht-9*M^2*he
    linear_combination h-c^3*hJU
  have hU : (ρ V)^3= -96*ρ e*(ρ H)^6*ρ U := by
    have h := congrArg ρ hJU
    change ρ (M^2*(t-3*e)*U)=ρ (V^3) at h
    simp only [map_mul,map_pow,map_sub,map_ofNat] at h
    rw [show ρ M= -4*(ρ H)^3 from hM,show ρ t= -3*ρ e from het] at h
    linear_combination -h
  rw [scale]
  exact pole_scaled p hp g hg e U H V he hH hV hU

open ZInQBlueprint.ResidualFactors ZInQBlueprint.ClusterParameters

/-- At a pole of a primitive input, the given integral parameter alone determines the six roots. -/
theorem pole_parameter (hp : 7≤p) (A B t : ℤ_[p]) (hab : IsUnit A ∨ IsUnit B)
    (g : ℕ) (hg : 0<g) (hv : addVal ℤ_[p] (poleForm A B)=(g:ℕ∞))
    (ht : t*m A B=n A B) :
    Nonempty (SexticFibre (monicSextic (fromPadics p t)) ((p:W)^g)) := by
  let φ := fromPadics p
  let ρ := residue W
  let τ := ρ.comp φ
  let : NeZero (2:κ) := ⟨small_residue p 2 (by decide) (by omega)⟩
  let : NeZero (3:κ) := ⟨small_residue p 3 (by decide) (by omega)⟩
  let : NeZero (5:κ) := ⟨small_residue p 5 (by decide) (by omega)⟩
  have hG0 : poleForm A B ≠ 0 := by
    intro h; rw [h,addVal_zero] at hv; exact ENat.natCast_ne_top _ hv.symm
  obtain ⟨k,V,e⟩ := eq_unit_mul_pow_irreducible hG0 PadicInt.irreducible_p
  have ek : k=g := ENat.natCast_inj.mp ((addVal_def _ V PadicInt.irreducible_p k e).symm.trans hv)
  have hGW : φ (poleForm A B) = (p:W)^g*φ (V:ℤ_[p]) := by
    rw [e,ek,map_mul,map_pow,map_natCast,mul_comm]
  obtain ⟨_,hc⟩ := uniformizer_scale p g hg
  have hg₀ : poleForm (τ A) (τ B)=0 := by
    have h := congrArg ρ hGW
    rw [map_mul,show ρ ((p:W)^g)=0 from hc,zero_mul] at h
    simpa [τ,poleForm,map_ofNat] using h
  have htAB : τ A ≠ 0 ∨ τ B ≠ 0 := hab.imp (fun h => (h.map τ).ne_zero) (fun h => (h.map τ).ne_zero)
  have hf : contactProduct (τ A) (τ B) ≠ 0 := fun h => separate_marks htAB h hg₀
  have hu : τ A+30*τ B ≠ 0 := fun h => hf (by simp [contactProduct,h])
  have hH : IsUnit (φ (A+30*B)) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa [τ,map_ofNat,ρ] using hu)
  have hm : ρ (φ (m A B))= -4*(ρ (φ (A+30*B)))^3 := by
    have h := m_congruence (τ A) (τ B)
    rw [hg₀,mul_zero] at h
    have h' : m (τ A) (τ B) = -4*(τ A+30*τ B)^3 := by linear_combination h
    simpa [m,τ,ρ,map_ofNat] using h'
  have hnorm : (m A B)^2*(t^2+27)=(poleForm A B)^3 := by
    calc _ = 27*(m A B)^2+(t*m A B)^2 := by ring
         _ = _ := by rw [ht]; exact (parameter_identities A B).2.1.symm
  apply pole_identity p hp g hg (φ t) (φ (m A B)) (φ (A+30*B)) (φ (V:ℤ_[p])) hH (V.isUnit.map φ) hm
  have h := congrArg φ hnorm
  simp only [map_mul,map_pow,map_add,map_ofNat] at h
  rw [hGW,mul_pow] at h
  exact h
end
end ZInQBlueprint.PrimitivePoleFibre
#print axioms ZInQBlueprint.PrimitivePoleFibre.pole_scaled
#print axioms ZInQBlueprint.PrimitivePoleFibre.pole_identity
#print axioms ZInQBlueprint.PrimitivePoleFibre.pole_parameter
