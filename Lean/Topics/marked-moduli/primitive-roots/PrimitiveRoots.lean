import DirectCharts
import PrimitiveLifts

/-! Fixed unramified quadratic fibres of the monic integral sextic. -/
namespace ZInQBlueprint.PrimitiveRoots
open Polynomial IsLocalRing IsDiscreteValuationRing
open ZInQBlueprint.PrimitiveLifts ZInQBlueprint.DirectCharts ZInQBlueprint.IntegralSextic
open ZInQBlueprint.ResidueExtension ZInQBlueprint.ClusterRoots
noncomputable section
variable {R : Type*} [CommRing R]
private def zeroPolynomial (a c U : R) : R[X] := zeroDivided (C a) (C c) (C U) X
private theorem zero_eval (a c U x : R) :
    (zeroPolynomial a c U).eval x = zeroDivided a c U x := by
  simp [zeroPolynomial,zeroDivided,beta,gamma]
private theorem zero_map {S : Type*} [CommRing S] (φ : R →+* S) (a c U : R) :
    (zeroPolynomial a c U).map φ = zeroPolynomial (φ a) (φ c) (φ U) := by
  simp [zeroPolynomial,zeroDivided,beta,gamma]
private theorem reduced_zero (U : R) :
    zeroPolynomial 0 0 U = C (27:R)*X^3+C (-36*U)*X ∧
    zeroPolynomial (-3) 0 U = C (-27:R)*X^3+C (-9*U)*X := by
  change zeroDivided (C 0) (C 0) (C U) X = _ ∧ zeroDivided (C (-3)) (C 0) (C U) X = _
  simpa only [map_zero,map_neg,map_mul,map_ofNat,sub_eq_add_neg,neg_mul] using zero_reduction (C U) X
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "κ" => ResidueField W
private instance henselian : HenselianRing W (IsLocalRing.maximalIdeal W) := by
  rw [ResidueExtension.maximalIdeal_eq]; infer_instance

private theorem zero_rows (hp : 7≤p) (U : ℤ_[p]) (hu : IsUnit U) :
    let u := residue W (fromPadics p U)
    Nonempty (SimpleTriple (C (27:κ)*X^3+C (-36*u)*X)) ∧
    Nonempty (SimpleTriple (C (-27:κ)*X^3+C (-9*u)*X)) := by
  let ρ := residue W
  let u := ρ (fromPadics p U)
  have hu0 : u ≠ 0 := ((residue_ne_zero_iff_isUnit _).mpr (hu.map (fromPadics p)))
  have h₂ : (2:κ) ≠ 0 := small_residue p 2 (by decide) (by omega)
  have h₃ : (3:κ) ≠ 0 := small_residue p 3 (by decide) (by omega)
  have h27 : (27:κ) ≠ 0 := by
    convert pow_ne_zero 3 h₃ using 1
    norm_num
  have hbu : IsUnit (3:ℤ_[p]) := small_unit p 3 (by decide) (by omega)
  obtain ⟨v,hv⟩ := padic_unit_square_root p (by omega) (3*U) (hbu.mul hu)
  obtain ⟨z,hz⟩ := padic_unit_square_root p (by omega) (-3*U) (hbu.neg.mul hu)
  have hv' : (ρ v)^2=3*u := by simpa [ρ,u,map_ofNat] using congrArg ρ hv
  have hz' : (ρ z)^2= -3*u := by simpa [ρ,u,map_ofNat] using congrArg ρ hz
  have hv0 : ρ v ≠ 0 := fun h => mul_ne_zero h₃ hu0 (by simpa [h] using hv'.symm)
  have hz0 : ρ z ≠ 0 := fun h => mul_ne_zero (neg_ne_zero.mpr h₃) hu0 (by simpa [h] using hz'.symm)
  change Nonempty (SimpleTriple (C (27:κ)*X^3+C (-36*u)*X)) ∧
    Nonempty (SimpleTriple (C (-27:κ)*X^3+C (-9*u)*X))
  constructor
  · apply symmetric (r:=2*ρ v/3) h27 (div_ne_zero (mul_ne_zero h₂ hv0) h₃) h₂
    field_simp
    linear_combination 108*hv'
  · apply symmetric (r:=ρ z/3) (neg_ne_zero.mpr h27) (div_ne_zero hz0 h₃) h₂
    field_simp
    linear_combination -27*hz'

/-- An even contact splits over the fixed unramified quadratic ring. -/
theorem even_contact (hp : 7≤p) (k : ℕ) (hk : 0<k) (U : ℤ_[p]) (hu : IsUnit U) :
    Nonempty (SexticFibre (monicSextic (((p:W)^k)^2*fromPadics p U)) ((p:W)^k)) := by
  let c := (p:W)^k
  let V := fromPadics p U
  let ρ := residue W
  let a : Fin 2 → W := ![0,-3]
  let g i := zeroPolynomial (a i) c V
  let P : Fin 2 → κ[X] := ![C (27:κ)*X^3+C (-36*ρ V)*X,C (-27:κ)*X^3+C (-9*ρ V)*X]
  obtain ⟨hc,hc₀⟩ := uniformizer_scale p k hk
  have h₃ : (3:κ) ≠ 0 := small_residue p 3 (by decide) (by omega)
  have ha : Function.Injective (fun i => ρ (a i)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a,ρ,map_ofNat]
  have hα (i) : alpha (a i) 1=0 := by fin_cases i <;> norm_num [a,alpha]
  obtain ⟨hm,hd⟩ := monic_six (c^2*V)
  apply lift_rows (a:=a) hc hc₀ ha hm.ne_zero hd.le g P
  · intro i x
    rw [monic_eval,zero_divided (hα i),zero_eval]
  · intro i
    change (zeroPolynomial _ _ _).map _ = _
    rw [zero_map,hc₀]
    fin_cases i
    · simpa [P,a,ρ] using (reduced_zero (ρ V)).1
    · simpa [P,a,ρ,map_ofNat] using (reduced_zero (ρ V)).2
  · intro i
    have H := zero_rows p hp U hu
    fin_cases i
    · exact H.1
    · exact H.2

theorem even_valuation (hp : 7≤p) (t : ℤ_[p]) (k : ℕ) (hk : 0<k)
    (hv : addVal ℤ_[p] t=((2*k:ℕ):ℕ∞)) :
    Nonempty (SexticFibre (monicSextic (fromPadics p t)) ((p:W)^k)) := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [addVal_zero] at hv
    exact ENat.natCast_ne_top _ hv.symm
  obtain ⟨m,u,e⟩ := eq_unit_mul_pow_irreducible ht PadicInt.irreducible_p
  have em : m=2*k := ENat.natCast_inj.mp ((addVal_def _ u PadicInt.irreducible_p m e).symm.trans hv)
  rw [e,em,map_mul,map_pow,map_natCast,show 2*k=k*2 by omega,pow_mul,mul_comm]
  exact even_contact p hp k hk u u.isUnit

end
end ZInQBlueprint.PrimitiveRoots
#print axioms ZInQBlueprint.PrimitiveRoots.even_contact
#print axioms ZInQBlueprint.PrimitiveRoots.even_valuation
