import SharpNumerics
import ContactPencil

namespace Sun28.HeightFibres.Sharp
open Sun28.FiveMarkUnits
noncomputable section
open private numberLog_le from PellSectors

theorem integral_pell (pell : PublishedPell312) (regulator : Regulator35) (disc : ConductorDiscriminants)
    {S : Finset ℕ} (pr : ∀ p∈S,p.Prime) {g h k a b c I J : ℤ} {T Z : ℝ}
    (one : 1≤T) (prod : (primeProduct S:ℝ)=T) (zp:0≤Z)
    (ng:g≠0) (nh:h≠0) (nk:k≠0)
    (gs:g.natAbs.primeFactors⊆S) (hs:h.natAbs.primeFactors⊆S) (ks:k.natAbs.primeFactors⊆S)
    (gT:(g.natAbs:ℝ)≤2^32*T) (hT:(h.natAbs:ℝ)≤2^32*T) (kT:(k.natAbs:ℝ)≤2^32*T)
    (i:I≠0) (j:J≠0) (ij:I≠J) (iZ:numberLog I≤Z) (jZ:numberLog J≤Z)
    (first:g*a^2-h*b^2=I) (second:g*a^2-k*c^2=J) :
    numberLog a≤2^170*T^2*(ell T)^7+2^160*T*(ell T)^4*Z := by
  obtain ⟨L,finite,dim,sr,sw,d⟩:=character_field ng nh nk pr gs hs ks disc
  let _ : FiniteDimensional ℚ L:=finite
  let D:ℝ:=(NumberField.discr L).natAbs
  have dp:1≤D:=by
    dsimp only [D]
    exact_mod_cast (show 1≤(NumberField.discr L).natAbs from Int.natAbs_pos.mpr (NumberField.discr_ne_zero L))
  have cap:D≤64*T^2 := by rw [←prod];dsimp only [D];exact_mod_cast d
  have r:=sharp_regulator one dp cap (regulator L dim)
  have bnd:=pell L dim g h k a b c I J ng nh nk i j ij sr sw first second _ _
    (numberLog_le ng gT) (numberLog_le nh hT) (numberLog_le nk kT) iZ jZ
  exact sharp_numeric one (NumberField.Units.regulator_pos L) r zp bnd

end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.integral_pell
