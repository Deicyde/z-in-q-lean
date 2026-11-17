import ClusterRoots
import WittBasis

/-! Singular sextic fibres over the ring of integers in one unramified quadratic
extension of ℚp. Neither branch requires a residual splitting hypothesis. -/
noncomputable section
namespace ZInQBlueprint.WittFibres
open Polynomial IsLocalRing ResidueExtension ClusterRoots SexticCalibration
open DiscEquations ResidualFactors

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "κ" => ResidueField W

private instance henselian : HenselianRing W (maximalIdeal W) := by
  rw [ResidueExtension.maximalIdeal_eq]; infer_instance

private theorem small_residue (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : κ) ≠ 0 := by
  intro h
  have h' := congrArg (residueFieldEquiv p) h
  simp only [map_natCast,map_zero] at h'
  exact (Nat.not_dvd_of_pos_of_lt hn hnp) ((CharP.cast_eq_zero_iff (QuadraticField p) p n).mp h')

private theorem small_unit (n : ℕ) (hn : 0 < n) (hnp : n < p) : IsUnit (n : ℤ_[p]) := by
  apply IsUnit.of_map (algebraMap ℤ_[p] W)
  rw [map_natCast]
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact small_residue p n hn hnp

private theorem scale (m : ℕ) (hm : 0 < m) :
    (p : W)^m ≠ 0 ∧ residue W ((p : W)^m) = 0 := by
  refine ⟨pow_ne_zero _ (uniformizer p).ne_zero, ?_⟩
  have h : residue W (p : W) = 0 := by
    apply (residueFieldEquiv p).injective
    rw [map_natCast,map_natCast,map_zero,CharP.cast_eq_zero]
  rw [map_pow,h,zero_pow hm.ne']

private theorem sqrt_unit {d : W} (hp : 11 ≤ p) (hd : d^2 = 6) : IsUnit d := by
  have h : IsUnit (6 : W) := by
    have hsix : IsUnit (6 : ℤ_[p]) := small_unit p 6 (by decide) (by omega)
    simpa only [map_ofNat] using hsix.map (fromPadics p)
  apply isUnit_of_dvd_unit (dvd_pow_self d (by decide : 2 ≠ 0))
  rwa [hd]

theorem sqrt_six (hp : 11 ≤ p) : ∃ d : W, d^2 = 6 := by
  simpa only [map_ofNat] using padic_unit_square_root p (by omega) (6 : ℤ_[p])
    (small_unit p 6 (by decide) (by omega))

/-- For any choice of square root of six, and each nonzero even contact depth
2m, the six roots form two triples over this fixed unramified quadratic ring. -/
theorem zero_contacts (hp : 11 ≤ p) (m : ℕ) (hm : 0 < m) (e : ℤ_[p]) (he : IsUnit e)
    (d : W) (hd : d^2 = 6) :
    Nonempty (SexticFibre (sextic (((p : W)^m)^2*(d*fromPadics p e))) ((p : W)^m)) := by
  let : NeZero (2 : κ) := ⟨small_residue p 2 (by decide) (by omega)⟩
  let : NeZero (3 : κ) := ⟨small_residue p 3 (by decide) (by omega)⟩
  have h48 : IsUnit (48 : ℤ_[p]) := by
    convert ((small_unit p 2 (by decide) (by omega)).pow 4).mul
      (small_unit p 3 (by decide) (by omega)) using 1; norm_num
  obtain ⟨v, hv⟩ := padic_unit_square_root p (by omega) (-(48:ℤ_[p])*e) (h48.neg.mul he)
  obtain ⟨z, hz⟩ := padic_unit_square_root p (by omega) ((48:ℤ_[p])*e) (h48.mul he)
  obtain ⟨hc,hc0⟩ := scale p m hm
  apply zero_fibre (u:=residue W (fromPadics p e)) (v:=residue W v) (z:=residue W z) hd hc hc0
  · exact map_mul _ _ _
  · exact (residue_ne_zero_iff_isUnit _).mpr ((sqrt_unit p hp hd).mul (he.map _))
  · simpa only [map_pow,map_mul,map_neg,map_ofNat] using congrArg (residue W) hv
  · simpa only [map_pow,map_mul,map_ofNat] using congrArg (residue W) hz

/-- The inverse parameter is constructed from the homogeneous input. Its scaled
value satisfies 240dF(c³U)=G³ in the integral ring and gives the six pole roots. -/
theorem pole_contacts (hp : 11 ≤ p) (m : ℕ) (hm : 0 < m) (A B D d : W)
    (hd : d^2=6) (hG : poleForm A B=(p:W)^m*D)
    (hB : IsUnit B) (hF : IsUnit (contactProduct A B)) (hD : IsUnit D) :
    ∃ U : W, IsUnit U ∧ 240*d*contactProduct A B*U=D^3 ∧
      240*d*contactProduct A B*(((p:W)^m)^3*U)=(poleForm A B)^3 ∧
      Nonempty (SexticFibre (polePolynomial (((p:W)^m)^3*U)) ((p:W)^m)) := by
  let : NeZero (2 : κ) := ⟨small_residue p 2 (by decide) (by omega)⟩
  let : NeZero (3 : κ) := ⟨small_residue p 3 (by decide) (by omega)⟩
  let : NeZero (5 : κ) := ⟨small_residue p 5 (by decide) (by omega)⟩
  let : NeZero (7 : κ) := ⟨small_residue p 7 (by decide) (by omega)⟩
  have h240 : IsUnit (240 : W) := by
    have h : IsUnit (240 : ℤ_[p]) := by
      convert (((small_unit p 2 (by decide) (by omega)).pow 4).mul
        (small_unit p 3 (by decide) (by omega))).mul (small_unit p 5 (by decide) (by omega))
        using 1; norm_num
    simpa only [map_ofNat] using h.map (fromPadics p)
  have hdF := (h240.mul (sqrt_unit p hp hd)).mul hF
  let U := (↑(hdF.unit⁻¹) : W)*D^3
  have hU : IsUnit U := (hdF.unit⁻¹).isUnit.mul (hD.pow 3)
  have hratio : 240*d*contactProduct A B*U=D^3 := by
    change 240*d*contactProduct A B*((↑(hdF.unit⁻¹):W)*D^3)=D^3
    calc
      _ = ((hdF.unit:W)*(↑(hdF.unit⁻¹):W))*D^3 := by rw [hdF.unit_spec]; ring
      _ = D^3 := by simp
  refine ⟨U,hU,hratio,?_,?_⟩
  · rw [hG,mul_pow,← hratio]; ring
  obtain ⟨s,hs⟩ := padic_unit_square_root p (by omega) (2 : ℤ_[p]) (small_unit p 2 (by decide) (by omega))
  have hs' : s^2=2 := by simpa only [map_ofNat] using hs
  obtain ⟨hc,hc0⟩ := scale p m hm
  apply pole_fibre (s:=s) (A:=residue W A) (B:=residue W B)
    (d:=residue W d) (D:=residue W D) hs' hc hc0
  · simpa only [map_pow,map_ofNat] using congrArg (residue W) hd
  · simpa only [poleForm,map_add,map_mul,map_pow,map_ofNat,hc0,zero_mul] using congrArg (residue W) hG
  · exact (residue_ne_zero_iff_isUnit _).mpr hB
  · simpa only [contactProduct,map_add,map_mul,map_ofNat] using (residue_ne_zero_iff_isUnit _).mpr hF
  · simpa only [contactProduct,map_add,map_mul,map_pow,map_ofNat] using congrArg (residue W) hratio
  · exact (residue_ne_zero_iff_isUnit _).mpr hU

/-- Without choosing an embedding of √6 in advance, the same extension works
for every positive contact scale, every base unit and both signs of √6. -/
theorem zero_both_signs (hp : 11 ≤ p) :
    ∃ d : W, d^2=6 ∧ ∀ (m : ℕ), 0 < m → ∀ e : ℤ_[p], IsUnit e →
      Nonempty (SexticFibre (sextic (((p:W)^m)^2*(d*fromPadics p e))) ((p:W)^m)) ∧
      Nonempty (SexticFibre (sextic (((p:W)^m)^2*((-d)*fromPadics p e))) ((p:W)^m)) := by
  obtain ⟨d,hd⟩ := sqrt_six p hp
  exact ⟨d,hd,fun m hm e he => ⟨zero_contacts p hp m hm e he d hd,
    zero_contacts p hp m hm e he (-d) (by simpa only [neg_sq] using hd)⟩⟩

/-- The pole input may be supplied over ℤp before choosing √6. -/
theorem padic_pole_contacts (hp : 11 ≤ p) (m : ℕ) (hm : 0 < m) (A B D : ℤ_[p])
    (hG : poleForm A B=(p:ℤ_[p])^m*D) (hB : IsUnit B)
    (hF : IsUnit (contactProduct A B)) (hD : IsUnit D) :
    ∃ d U : W, d^2=6 ∧ IsUnit U ∧ 240*d*fromPadics p (contactProduct A B)*U=(fromPadics p D)^3 ∧
      240*d*fromPadics p (contactProduct A B)*(((p:W)^m)^3*U)=(fromPadics p (poleForm A B))^3 ∧
      Nonempty (SexticFibre (polePolynomial (((p:W)^m)^3*U)) ((p:W)^m)) := by
  obtain ⟨d,hd⟩ := sqrt_six p hp
  have G : poleForm (fromPadics p A) (fromPadics p B) = fromPadics p (poleForm A B) := by
    simp [poleForm,map_ofNat]
  have F : contactProduct (fromPadics p A) (fromPadics p B) = fromPadics p (contactProduct A B) := by
    simp [contactProduct,map_ofNat]
  have hG' : poleForm (fromPadics p A) (fromPadics p B)=(p:W)^m*fromPadics p D := by
    rw [G,hG,map_mul,map_pow,map_natCast]
  obtain ⟨U,hU,h1,h2,hT⟩ := pole_contacts p hp m hm _ _ _ d hd hG' (hB.map _) (F ▸ hF.map _) (hD.map _)
  exact ⟨d,U,hd,hU,F ▸ h1,F ▸ G ▸ h2,hT⟩

end ZInQBlueprint.WittFibres
#print axioms ZInQBlueprint.WittFibres.sqrt_six
#print axioms ZInQBlueprint.WittFibres.zero_contacts
#print axioms ZInQBlueprint.WittFibres.pole_contacts

#print axioms ZInQBlueprint.WittFibres.zero_both_signs
#print axioms ZInQBlueprint.WittFibres.padic_pole_contacts
