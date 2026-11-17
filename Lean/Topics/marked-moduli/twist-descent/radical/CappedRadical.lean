import MordellSectors
import Mathlib.RingTheory.Radical.NatInt

/-! The integral case of the published Mordell bound and the conductor
factor for the two Mordell curves attached to the six-contact descent. -/
open UniqueFactorizationMonoid
namespace ZInQBlueprint.TwistDescent
noncomputable section

/-- The function r₂ in von Känel 2014, Section 7.3.2, with S empty. -/
def cappedPart (A : ℕ) : ℕ := ∏ p ∈ A.primeFactors, p ^ min 2 (A.factorization p)

/-- Corollary 7.4 at S empty for a positive integral abscissa. -/
def IntegralMordell74 : Prop :=
  ∀ (a X Y : ℤ), a≠0 → 0<X → Y^2=X^3+a →
    let aS : ℝ := 62208*(cappedPart a.natAbs:ℝ)
    Real.log (X:ℝ) ≤ Real.log (a.natAbs:ℝ)+4*aS*(Real.log aS)^2

theorem cappedPart_pos (A : ℕ) : 0<cappedPart A :=
  Finset.prod_pos (fun _ hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _)

theorem cappedPart_le_radical_sq (A : ℕ) : cappedPart A ≤ radical A ^ 2 := by
  rw [cappedPart,Nat.radical_eq_prod_primeFactors,←Finset.prod_pow]
  exact Finset.prod_le_prod (fun p hp => Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors hp)
    (min_le_left _ _))

private theorem radical_mul_le (a b : ℕ) : radical (a*b) ≤ radical a*radical b :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos a) (Nat.radical_pos b)) radical_mul_dvd

theorem capped_mordell_radical (u l : ℤ) :
    cappedPart (-27*u^2*l^4).natAbs ≤ 9*(radical u.natAbs)^2*(radical l.natAbs)^2 := by
  have r27 : radical (27:ℕ)=3 := by
    rw [show (27:ℕ)=3^3 by decide,radical_pow _ (by decide)]
    exact radical_of_prime (Nat.prime_iff.mp (by decide : Nat.Prime 3))
  let U := u.natAbs
  let L := l.natAbs
  have r : radical (27*U^2*L^4) ≤ 3*radical U*radical L := calc
    _ ≤ (radical 27*radical (U^2))*radical (L^4) :=
      (radical_mul_le _ _).trans (Nat.mul_le_mul_right _ (radical_mul_le _ _))
    _ = 3*radical U*radical L := by rw [r27,radical_pow _ (by decide),radical_pow _ (by decide)]
  simp only [Int.natAbs_mul,Int.natAbs_pow,show (-27:ℤ).natAbs=27 by decide]
  change cappedPart (27*U^2*L^4) ≤ 9*(radical U)^2*(radical L)^2
  calc
    _ ≤ (3*radical U*radical L)^2 := (cappedPart_le_radical_sq _).trans (Nat.pow_le_pow_left r 2)
    _ = _ := by ring

/-- Keep the selected coefficient and multiplier as separate integers for
applying the truncated exponents to the actual integral Mordell model. -/
theorem selected_mordell {r v m n T : ℤ} (sr : Squarefree r) (sv : Squarefree v)
    (mn : m≠0) (nn : n≠0) (tp : 0<T) (eq : r^2*m^4+27*v^2*n^4=T^3) :
    ∃ u l X Y : ℤ, u≠0 ∧ l≠0 ∧ 0<X ∧ T≤X ∧ Y^2=X^3+(-27*u^2*l^4) ∧
      u.natAbs ≤ r.natAbs*v.natAbs ∧ l.natAbs = min m.natAbs n.natAbs := by
  rcases le_total m.natAbs n.natAbs with h|h
  · refine ⟨r,m,3*T,27*v*n^2,sr.ne_zero,mn,by omega,by omega,?_,?_,(min_eq_left h).symm⟩
    · linear_combination 27*eq
    · simpa only [mul_one] using Nat.mul_le_mul_left r.natAbs (show 1≤v.natAbs from Int.natAbs_pos.mpr sv.ne_zero)
  · refine ⟨v,n,T,r*m^2,sv.ne_zero,nn,tp,le_rfl,?_,?_,(min_eq_right h).symm⟩
    · linear_combination eq
    · simpa only [one_mul] using Nat.mul_le_mul_right v.natAbs (show 1≤r.natAbs from Int.natAbs_pos.mpr sr.ne_zero)

#print axioms cappedPart_pos
#print axioms cappedPart_le_radical_sq
#print axioms capped_mordell_radical
#print axioms selected_mordell
end
end ZInQBlueprint.TwistDescent
