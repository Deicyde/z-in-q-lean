import AbscissaDivisor
import LocalAbscissaMask
import PeriodWindowRows

namespace Sun28.Abscissa
open Sun28.SelmerRealization Sun28.SeededPartners Sun28.NormPartners Sun28.GlobalSections
open Sun28.PairedClasses Sun28.MarkedOdd Sun28.PeriodWindows Sun28.QualitativeRows
open ZInQ.RouteK ZInQ.RouteK.Selmer ZInQ
open ZInQBlueprint.FiveMetric ZInQBlueprint.DiamondHeight ZInQBlueprint.CMPeriods ZInQBlueprint.IntegralSections
noncomputable section

/-- The second equation of the odd local descent matrix at p. -/
def unitRow (l m p : ℕ) : Prop :=
  ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
    legBit p (primeUnit p (m:ℤ)) = (exponent p (m:ℤ) : ZMod 2)*legBit p (-((l:ℤ)/p))

/-- A finite set of positive squarefree descent labels, given the prime divisors of l. -/
def labels (l : ℕ) : Finset ℕ := by
  classical
  exact l.divisors.filter (fun m => 1 < m ∧ m%3=1 ∧
    (∀ p∈m.primeFactors,p%3=1) ∧ ∀ p∈l.primeFactors,unitRow l m p)

private theorem good_prime {l p : ℕ} (res : l%12=11) (hp : p.Prime) (pl : p∣l) : 3 < p := by
  have := hp.two_le
  by_contra! h
  interval_cases p <;> omega

private theorem label_product {b m : ℕ} (bp : 0 < b) (mp : 0 < m) (p : ℕ) [Fact p.Prime] :
    SqEq (((sqf ((b:ℚ)*m) : ℤ):Qp p)*m) b := by
  let a:=sqf ((b:ℚ)*m)
  have mn : (m:ℚ)≠0 := by exact_mod_cast mp.ne'
  have bn : (b:ℚ)≠0 := by exact_mod_cast bp.ne'
  obtain ⟨_,t,tn,T⟩:=sqf_spec (mul_ne_zero bn mn)
  change (b:ℚ)*m=(a:ℚ)*t^2 at T
  have H : (a:ℚ)*m=b*((m:ℚ)/t)^2 := by
    field_simp
    linear_combination -T
  refine ⟨algebraMap ℚ (Qp p) ((m:ℚ)/t), (map_ne_zero (algebraMap ℚ (Qp p))).mpr (div_ne_zero mn tn),?_⟩
  simpa only [map_mul,map_natCast,map_intCast,map_pow] using congrArg (algebraMap ℚ (Qp p)) H

open private shapes from CompanionExclusion in
/-- On a residual pair, a strict point on the seeded second twist is equivalent
to rational solubility of one explicitly restricted pair of diagonal quadrics. -/
theorem strict_iff_label {b d q:ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (ex : ¬CancelledFactors b d) : strictPoint b (b*q*d) ↔
      ∃ m∈labels (b*q*d), Cover ℚ (b*q*d) (sqf ((b:ℚ)*m)) m := by
  classical
  obtain ⟨hb,hk,sf'⟩ := shapes ad C
  have sf : Squarefree (b*q*d) := by simpa only [Nat.mul_assoc] using sf'
  constructor
  · rintro ⟨u,y,un,yn,H⟩
    obtain ⟨m,D,S⟩:=divisor_of_strict_coordinates ad.1 C.companion_residue un yn H
    have m1 : m≠1 := by
      rintro rfl
      apply necessary_nonsquare ad C ex un yn H
      by_cases zero : (b:ℚ)*u^2-(b*q*d:ℕ)=0
      · exact ⟨0,by simpa only [mul_zero] using zero⟩
      obtain ⟨_,v,_,V⟩ := sqf_spec zero
      rw [S] at V
      exact ⟨v,by simpa [pow_two] using V⟩
    have bm : (b:ℚ)*m≠0 := mul_ne_zero (by exact_mod_cast ad.1.ne') (by exact_mod_cast D.positive.ne')
    refine ⟨m,Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨D.divides,sf.ne_zero⟩,
      by have := D.positive;omega,D.mod_three,?_,?_⟩,D.rational⟩
    · intro p mem
      have hp:=Nat.prime_of_mem_primeFactors mem
      have : Fact p.Prime := ⟨hp⟩
      have pm := Nat.dvd_of_mem_primeFactors mem
      have pl := dvd_trans pm D.divides
      have large := good_prime C.companion_residue hp pl
      exact prime_one_mod_three large (split_of_ramified large sf pl pm D.divides ad.1
        (C.local_second.2.2.2 p) (cover_map D.rational) (label_product ad.1 D.positive p))
    · intro p mem hp
      have : Fact p.Prime := ⟨hp⟩
      have pl:=Nat.dvd_of_mem_primeFactors mem
      have large:=good_prime C.companion_residue hp pl
      exact (bad_rows (by omega) (by omega) pl sf (sqf_spec bm).1
        (Int.squarefree_natCast.mpr (sf.squarefree_of_dvd D.divides)) (cover_map D.rational)).2
  · rintro ⟨m,mem,H⟩
    obtain ⟨div,m1,mod3,_⟩:=Finset.mem_filter.mp mem
    exact strict_of_divisor hb hk (Nat.mul_assoc ..) sf
      ⟨by omega,(Nat.mem_divisors.mp div).1,mod3,H⟩

def DivisorCompanion : Prop :=
  ∀ b d : ℕ, Residual b d → ∃ q, Candidate b d q ∧
    ∃ m∈labels (b*q*d), Cover ℚ (b*q*d) (sqf ((b:ℚ)*m)) m

theorem divisor_companion_iff : DivisorCompanion ↔ WeakCompanion := by
  constructor
  · intro lift b d r
    obtain ⟨q,C,h⟩:=lift b d r
    exact ⟨q,C,(strict_iff_label r.1 C r.2.2.2.2.2.2.2).mpr h⟩
  · intro lift b d r
    obtain ⟨q,C,h⟩:=lift b d r
    exact ⟨q,C,(strict_iff_label r.1 C r.2.2.2.2.2.2.2).mp h⟩

set_option maxRecDepth 14000
set_option exponentiation.threshold 250
set_option maxHeartbeats 600000
/-- Composition of the signed polynomial, the point orders in each real window,
and the finite list of possible second descent labels at each chosen seed. -/
theorem one_sign_of_divisor_windows (table : SmallClassDiscriminants) (fibres : ActualPencilFibres (210^300))
    (realCurves : RealComponents.PublishedProposition72)
    (windows : ∀ k, ∃ F : PeriodFrame (integerWindow realCurves k) 576,
      ∀ i, ¬(active F.orders (Nat.factorial 576) i true ∧ active F.orders (Nat.factorial 576) i false))
    (lift : DivisorCompanion) (x:ℚ) :
    (∃ v : Fin 28 → ℚ, Sun28.eval28 Sun28.MultiplierChoice.oneSignPolynomial x v=0) ↔ ∃ k : ℤ,x=(k:ℚ) := by
  apply one_sign_of_weak_companion table fibres realCurves _ (divisor_companion_iff.mp lift) x
  intro k
  obtain ⟨F,h⟩:=windows k
  exact point_row_of_one_arm F h

end
end Sun28.Abscissa

#print axioms Sun28.Abscissa.strict_iff_label
#print axioms Sun28.Abscissa.divisor_companion_iff
#print axioms Sun28.Abscissa.one_sign_of_divisor_windows
