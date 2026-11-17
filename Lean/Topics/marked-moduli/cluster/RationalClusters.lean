import PadicParameters
import ClusterPicture

/-! Both singular charts of the sextic at its literal rational parameter. -/
namespace ZInQBlueprint.RationalClusters
open ZInQBlueprint.ResidueExtension ZInQBlueprint.ClusterParameters ZInQBlueprint.PadicParameters
open ZInQBlueprint.ResidualFactors ZInQBlueprint.ClusterRoots ZInQBlueprint.SexticCalibration
open ZInQBlueprint.DiscEquations IsDiscreteValuationRing
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "L" => LocalField p
local notation "ι" => algebraMap W L
local notation "ιq" => RingHom.comp (algebraMap ℚ_[p] L) (algebraMap ℚ ℚ_[p])
abbrev F (u : ℚ) := contactProduct (u.num:ℤ_[p]) (u.den:ℤ_[p])
abbrev G (u : ℚ) := poleForm (u.num:ℤ_[p]) (u.den:ℤ_[p])

theorem mapped_parameter (u : ℚ) : ιq (CoarseConic.r u) =
    240*ι (fromPadics p (F p u))/(ι (fromPadics p (G p u)))^3 := by
  have hB : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have h := congrArg ιq (rational_parameter (u.num:ℚ) (u.den:ℚ) hB)
  rw [Rat.num_div_den] at h
  simpa only [F,G,contactProduct,poleForm,map_div₀,map_mul,map_add,map_pow,map_ofNat,map_natCast,map_intCast] using h

private lemma denominator_ne_zero (u : ℚ) : ι (fromPadics p (G p u)) ≠ 0 := by
  have hB : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have h := (homogenize (u.num:ℚ) (u.den:ℚ) hB).2
  rw [Rat.num_div_den] at h
  have hn : poleForm (u.num:ℚ) (u.den:ℚ) ≠ 0 :=
    h ▸ mul_ne_zero (SixContact.positive_denominator u).ne' (pow_ne_zero _ hB)
  have hn' := (map_ne_zero_iff ιq (ιq).injective).mpr hn
  simpa only [G,poleForm,map_mul,map_add,map_pow,map_ofNat,map_natCast,map_intCast] using hn'

/-- Positive even contact gives the sextic at the literal scalar √6 r(u). -/
theorem even_rational (hp : 11 ≤ p) (u : ℚ) (k : ℕ) (hk : 0<k)
    (hv : addVal ℤ_[p] (F p u)=((2*k:ℕ):ℕ∞)) (d : W) (hd : d^2=6) :
    ∃ s : W, ι s = ι d*ιq (CoarseConic.r u) ∧ Nonempty (SexticFibre (sextic s) ((p:W)^k)) := by
  obtain ⟨s,_,he,T⟩ := primitive_zero hp _ _ (rational_primitive u) k hk hv d hd
  refine ⟨s,?_,T⟩
  change (fromPadics p (G p u))^3*s = 240*d*fromPadics p (F p u) at he
  have H := congrArg ι he
  simp only [map_mul,map_pow,map_ofNat] at H
  rw [mapped_parameter,← mul_div_assoc,eq_div_iff (pow_ne_zero _ (denominator_ne_zero p u))]
  linear_combination H

/-- At a pole the integral sextic uses the inverse of the literal parameter √6 r(u). -/
theorem pole_rational (hp : 11 ≤ p) (u : ℚ) (g : ℕ) (hg : 0<g)
    (hv : addVal ℤ_[p] (G p u)=(g:ℕ∞)) :
    ∃ d w : W, d^2=6 ∧ ι w*(ι d*ιq (CoarseConic.r u))=1 ∧
      Nonempty (SexticFibre (polePolynomial w) ((p:W)^g)) := by
  obtain ⟨d,w,hd,he,T⟩ := primitive_pole hp _ _ (rational_primitive u) g hg hv
  refine ⟨d,w,hd,?_,T⟩
  change 240*d*fromPadics p (F p u)*w=(fromPadics p (G p u))^3 at he
  have H := congrArg ι he
  simp only [map_mul,map_pow,map_ofNat] at H
  rw [mapped_parameter,← mul_div_assoc,← mul_div_assoc,div_eq_one_iff_eq (pow_ne_zero _ (denominator_ne_zero p u))]
  linear_combination H

end
end ZInQBlueprint.RationalClusters
#print axioms ZInQBlueprint.RationalClusters.mapped_parameter
#print axioms ZInQBlueprint.RationalClusters.even_rational
#print axioms ZInQBlueprint.RationalClusters.pole_rational
