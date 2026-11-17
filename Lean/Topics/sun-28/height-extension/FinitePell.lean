import PublishedDeep
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! The published S-integer simultaneous-Pell inequality for rational coordinates
over a biquadratic field. S consists of all infinite places and the primes over P. -/
namespace Sun28.HeightExtension
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.FiveMarkUnits Height
noncomputable section

structure PlacesData where
  regulator : ℝ
  logarithmQ : ℝ
  primeNorm : ℝ
  regulator_pos : 0<regulator
  one_le_primeNorm : 1≤primeNorm

/-- Lemma 3.5 (3.6),(3.7), for fields of degree at most four. -/
def PublishedClassRegulator : Prop :=
  ∀ (L : IntermediateField ℚ Omega) [FiniteDimensional ℚ L], Module.finrank ℚ L≤4 →
    let D:ℝ:=(NumberField.discr L).natAbs
    (1/5:ℝ)≤NumberField.Units.regulator L ∧
      (NumberField.classNumber L:ℝ)*NumberField.Units.regulator L≤Real.sqrt D*(logStar D)^3

/-- The all-places-over-P specialization of Bérczes–Evertse–Győry (3.14).
Every rational variable here is an S-integer exactly when its reduced
denominator is supported in P. The conclusion uses only the first height. -/
def PublishedFinitePell : Prop :=
  ∀ (L : IntermediateField ℚ Omega) [FiniteDimensional ℚ L], Module.finrank ℚ L≤4 →
    ∀ (P : Finset ℕ), (∀ p∈P,p.Prime) → P.card≤4 →
    ∃ a : PlacesData,
      a.primeNorm≤(primeProduct P:ℝ)^4 ∧ 0≤a.logarithmQ ∧ a.logarithmQ≤4*Real.log (primeProduct P:ℝ) ∧
      a.regulator≤(NumberField.classNumber L:ℝ)*NumberField.Units.regulator L*
        (max 1 (4*Real.log (primeProduct P:ℝ)))^16 ∧
    ∀ (g h k I J : ℤ) (x y z : ℚ), g≠0 → h≠0 → k≠0 → I≠0 → J≠0 → I≠J →
      (∃ r:L,r^2=(g:L)/(h:L)) → (∃ w:L,w^2=(g:L)/(k:L)) →
      x.den.primeFactors⊆P → y.den.primeFactors⊆P → z.den.primeFactors⊆P →
      (g:ℚ)*x^2-(h:ℚ)*y^2=(I:ℚ) → (g:ℚ)*x^2-(k:ℚ)*z^2=(J:ℚ) →
      ∀ H B:ℝ, numberLog g≤H → numberLog h≤H → numberLog k≤H → numberLog I≤B → numberLog J≤B →
      logHeight₁ x ≤ 2^512*a.primeNorm*a.regulator*(1+logStar a.regulator)*
        (NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*a.logarithmQ+4*H+B)

open private numberLog_le from PellSectors

theorem prime_product_pos {S : Finset ℕ} (pr : ∀ p∈S,p.Prime) : 0<primeProduct S :=
  Finset.prod_pos (fun p hp=>(pr p hp).pos)

/-- The original squarefree-prime product controls the class number and the
ordinary regulator jointly. Friedman’s one-fifth lower bound controls the
class number separately. -/
theorem class_bounds (published : PublishedClassRegulator)
    (L : IntermediateField ℚ Omega) [FiniteDimensional ℚ L] (dim : Module.finrank ℚ L≤4)
    {T : ℝ} (one : 1≤T) (cap:((NumberField.discr L).natAbs:ℝ)≤64*T^2) :
    let r:=NumberField.Units.regulator L
    let h:ℝ:=NumberField.classNumber L
    h*r≤2^12*T*(ell T)^3 ∧ r≤2^12*T*(ell T)^3 ∧ h≤5*2^12*T*(ell T)^3 := by
  let r:=NumberField.Units.regulator L
  let h:ℝ:=NumberField.classNumber L
  have ⟨low,up⟩:=published L dim
  have dp:1≤((NumberField.discr L).natAbs:ℝ):=by exact_mod_cast
    (show 1≤(NumberField.discr L).natAbs from Int.natAbs_pos.mpr (NumberField.discr_ne_zero L))
  have hr:h*r≤2^12*T*(ell T)^3:=sharp_regulator one dp cap up
  have hp:1≤h:=Nat.one_le_cast.mpr (NumberField.classNumber_pos L)
  have rr:r≤h*r:=by simpa using mul_le_mul_of_nonneg_right hp (NumberField.Units.regulator_pos L).le
  have hh:=mul_le_mul_of_nonneg_left low (show 0≤h by linarith)
  change h*(1/5)≤h*r at hh
  exact ⟨hr,rr.trans hr,by linarith only [hr,hh]⟩

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.class_bounds
