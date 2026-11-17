import ClusterParameters
import WittFibres
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-! Recover the local units and parameters from the valuations of a primitive pair. -/
namespace ZInQBlueprint.PadicParameters
open IsDiscreteValuationRing ZInQBlueprint.ResidualFactors ZInQBlueprint.ClusterParameters
variable {p : ℕ} [Fact p.Prime]

private lemma units_mod (x : ℤ_[p]) : PadicInt.toZMod x ≠ 0 ↔ IsUnit x := by
  rw [Ne,← RingHom.mem_ker,PadicInt.ker_toZMod,IsLocalRing.mem_maximalIdeal]
  change (¬ ¬ IsUnit x) ↔ IsUnit x
  simp

private lemma residue_prime (n : ℕ) (h : 0 < n) (h' : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne,CharP.cast_eq_zero_iff (ZMod p) p]
  exact Nat.not_dvd_of_pos_of_lt h h'

private theorem unit_factor {x : ℤ_[p]} {m : ℕ}
    (hx : addVal ℤ_[p] x = (m:ℕ∞)) : ∃ u : ℤ_[p]ˣ, x = (p:ℤ_[p])^m*(u:ℤ_[p]) := by
  have hn : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨n,u,hu⟩ := eq_unit_mul_pow_irreducible hn PadicInt.irreducible_p
  have h := (addVal_def x u PadicInt.irreducible_p n hu).symm.trans hx
  have he : n=m := ENat.natCast_inj.mp h
  exact ⟨u,by rw [← he,hu,mul_comm]⟩

private lemma mod_scale (m : ℕ) (hm : 0 < m) : PadicInt.toZMod ((p:ℤ_[p])^m)=0 := by
  simp [hm.ne']

private lemma prim (A B : ℤ_[p]) (h : IsUnit A ∨ IsUnit B) :
    PadicInt.toZMod A ≠ 0 ∨ PadicInt.toZMod B ≠ 0 := h.imp (units_mod _).mpr (units_mod _).mpr
/-- At even contact one base unit e satisfies G³ p^(2k) e = 240 F. -/
theorem even_contact_data (hp : 11 ≤ p) (A B : ℤ_[p]) (hab : IsUnit A ∨ IsUnit B)
    (k : ℕ) (hk : 0<k) (hv : addVal ℤ_[p] (contactProduct A B) = ((2*k:ℕ):ℕ∞)) :
    IsUnit (poleForm A B) ∧ ∃ e : ℤ_[p]ˣ, (poleForm A B)^3 * ((p:ℤ_[p])^k)^2 * (e:ℤ_[p]) = 240*contactProduct A B := by
  let : NeZero (2:ZMod p) := ⟨residue_prime 2 (by decide) (by omega)⟩
  let : NeZero (3:ZMod p) := ⟨residue_prime 3 (by decide) (by omega)⟩
  let : NeZero (5:ZMod p) := ⟨residue_prime 5 (by decide) (by omega)⟩
  obtain ⟨v,hv⟩ := unit_factor hv
  have hf : contactProduct (PadicInt.toZMod A) (PadicInt.toZMod B)=0 := by
    have h := congrArg PadicInt.toZMod hv
    rw [map_mul,mod_scale _ (by omega),zero_mul] at h
    simpa [contactProduct,map_ofNat] using h
  have hG : IsUnit (poleForm A B) := (units_mod _).1 (by
    simpa [poleForm,map_ofNat] using separate_marks (prim A B hab) hf)
  have h240 : IsUnit (240:ℤ_[p]) := (units_mod _).1 (by
    rw [map_ofNat, show (240:ZMod p)=2^4*3*5 by norm_num]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne _)) (NeZero.ne _)) (NeZero.ne _))
  refine ⟨hG,h240.unit*v*(hG.unit⁻¹)^3, ?_⟩
  have cancel : (poleForm A B)^3 * ((↑(hG.unit⁻¹):ℤ_[p])^3)=1 := by
    calc _ = ((↑hG.unit:ℤ_[p])*↑hG.unit⁻¹)^3 := by simp only [mul_pow,hG.unit_spec]
         _ = 1 := by simp
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,h240.unit_spec]
  rw [hv,show 2*k=k*2 by omega,pow_mul]
  linear_combination (240:ℤ_[p]) * ((p:ℤ_[p])^k)^2 * (v:ℤ_[p]) * cancel

/-- At a pole, primitive coordinates supply all three units in the pole chart. -/
theorem pole_data (hp : 11 ≤ p) (A B : ℤ_[p]) (hab : IsUnit A ∨ IsUnit B)
    (m : ℕ) (hm : 0 < m) (hv : addVal ℤ_[p] (poleForm A B)=(m:ℕ∞)) :
    IsUnit B ∧ IsUnit (contactProduct A B) ∧
      ∃ D : ℤ_[p]ˣ, poleForm A B=(p:ℤ_[p])^m*(D:ℤ_[p]) := by
  let : NeZero (2:ZMod p) := ⟨residue_prime 2 (by decide) (by omega)⟩
  let : NeZero (3:ZMod p) := ⟨residue_prime 3 (by decide) (by omega)⟩
  let : NeZero (5:ZMod p) := ⟨residue_prime 5 (by decide) (by omega)⟩
  let : NeZero (7:ZMod p) := ⟨residue_prime 7 (by decide) (by omega)⟩
  obtain ⟨D,hD⟩ := unit_factor hv
  have hg : poleForm (PadicInt.toZMod A) (PadicInt.toZMod B)=0 := by
    have h := congrArg PadicInt.toZMod hD
    rw [map_mul,mod_scale _ hm,zero_mul] at h
    simpa [poleForm,map_ofNat] using h
  obtain ⟨hb,hf⟩ := ClusterParameters.pole_units (prim A B hab) hg
  exact ⟨(units_mod _).mp hb,(units_mod _).mp (by simpa [contactProduct,map_ofNat] using hf),D,hD⟩

/-- The canonical numerator and denominator are primitive at every prime. -/
theorem rational_primitive (u : ℚ) : IsUnit (u.num : ℤ_[p]) ∨ IsUnit (u.den : ℤ_[p]) := by
  have hc : IsCoprime u.num (u.den:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using u.reduced)
  obtain ⟨x,y,h⟩ := hc.map (Int.castRingHom ℤ_[p])
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one h).imp isUnit_of_mul_isUnit_right
    (fun h => by simpa using isUnit_of_mul_isUnit_right h)

open ZInQBlueprint.ResidueExtension ZInQBlueprint.WittFibres ZInQBlueprint.ClusterRoots
open ZInQBlueprint.SexticCalibration ZInQBlueprint.DiscEquations
local notation "W" => IntegralField p

/-- The integral parameter s of an even contact satisfies the rational family's defining identity. -/
theorem primitive_zero (hp : 11 ≤ p) (A B : ℤ_[p]) (hab : IsUnit A ∨ IsUnit B)
    (k : ℕ) (hk : 0<k) (hv : addVal ℤ_[p] (contactProduct A B) = ((2*k:ℕ):ℕ∞))
    (d : W) (hd : d^2=6) : ∃ s : W, IsUnit (fromPadics p (poleForm A B)) ∧
    (fromPadics p (poleForm A B))^3*s = 240*d*fromPadics p (contactProduct A B) ∧
    Nonempty (SexticFibre (sextic s) ((p:W)^k)) := by
  obtain ⟨hg,e,he⟩ := even_contact_data (by omega) A B hab k hk hv
  refine ⟨((p:W)^k)^2*(d*fromPadics p (e:ℤ_[p])),hg.map _,?_,
    zero_contacts p hp k hk e e.isUnit d hd⟩
  have h := congrArg (fromPadics p) he
  simp only [map_mul,map_pow,map_natCast,map_ofNat] at h
  linear_combination d*h

/-- A pole order alone specifies the inverse parameter w and the two root triples. -/
theorem primitive_pole (hp : 11 ≤ p) (A B : ℤ_[p]) (hab : IsUnit A ∨ IsUnit B)
    (g : ℕ) (hg : 0<g) (hv : addVal ℤ_[p] (poleForm A B) = (g:ℕ∞)) :
    ∃ d w : W, d^2=6 ∧ 240*d*fromPadics p (contactProduct A B)*w =
      (fromPadics p (poleForm A B))^3 ∧ Nonempty (SexticFibre (polePolynomial w) ((p:W)^g)) := by
  obtain ⟨hb,hf,D,hD⟩ := pole_data (by omega) A B hab g hg hv
  obtain ⟨d,U,hd,_,_,he,hT⟩ := padic_pole_contacts p hp g hg A B D hD hb hf D.isUnit
  exact ⟨d,((p:W)^g)^3*U,hd,he,hT⟩

end ZInQBlueprint.PadicParameters
#print axioms ZInQBlueprint.PadicParameters.even_contact_data
#print axioms ZInQBlueprint.PadicParameters.pole_data
#print axioms ZInQBlueprint.PadicParameters.rational_primitive
#print axioms ZInQBlueprint.PadicParameters.primitive_zero
#print axioms ZInQBlueprint.PadicParameters.primitive_pole
