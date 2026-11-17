import PeriodFixedPins
import GeneratorRows

namespace Sun28.PeriodWindows
open Sun28.QualitativeRows Sun28.ContactFactors Sun28.ContactSieve Sun28.ScalarPlaces
open Sun28.FixedPreparation Sun28.RealPoleBounds Sun28.GaussianSelection Sun28.Exceptional
open Sun28.Forward Sun28.FiniteWitness Sun28.ScalarHeight Sun28.Ordinary
open ManuscriptV15.Arithmetic
noncomputable section

/-- A single rational prime, with two CM rays, absence of odd self-intersection,
and freedom from the fixed odd primes. All conditions concern this prime alone. -/
def cleanPrime (K p : ℕ) : Prop :=
  p.Prime ∧ ∃ z : Gaussian, gaussianNorm z=p ∧ gaussianCongruent 16 z (9,0) ∧
    gaussianCongruent 7 z (1,3) ∧
    (∀ q, q.Prime → q≠2 → ¬(q∣adjacentNorm z true ∧ q∣adjacentNorm z false)) ∧
    (∀ q, q.Prime → q≠2 → q≤K → ∀ s,¬q∣adjacentNorm z s)

/-- All data other than relations between different marked rational primes.
The roots apply simultaneously to every occurrence of a repeated mark. -/
structure PeriodFrame {X : ℤ} (w : Window X) (L : ℕ) where
  u : ℕ
  v : ℕ
  values : PrimeValues (fixedScale w.n) u v
  pos : 0<v
  step : requiredDivisor (fixedScale w.n) ∣ v
  slope_large : slopeThreshold (fixedScale w.n) w.C (1/2) < (slope (fixedScale w.n) u v : ℝ)
  rays : Sun28.TwistRank.RayValues values
  exclusions : ∀ j,∀ p∈selected values j, ¬p∣dilation (fixedScale w.n) ∧ ¬p∣separation ∧
    padicValRat p (fixedScale w.n j)=0
  roots : (i : ↥(shifts (fixedScale w.n))) → ZMod (values.value i)
  squares : ∀ i,(roots i)^2=2
  individual : ∀ i, (periodAt values (fun d h=>(rays d h).1) roots squares i false).gcd
      (periodAt values (fun d h=>(rays d h).1) roots squares i true) ∣ Nat.factorial 576
  dyadic : ∀ i s,padicValNat 2 (periodAt values (fun d h=>(rays d h).1) roots squares i s)≤6
  free : ∀ q, q.Prime → q≠2 → q≤guard (integerRadicand X) L →
    ∀ i s,¬q∣periodAt values (fun d h=>(rays d h).1) roots squares i s

def PeriodFrame.orders {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L) :=
  periodAt F.values (fun d h=>(F.rays d h).1) F.roots F.squares

theorem PeriodFrame.shared_above {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L)
    {q : ℕ} (h : shared F.orders (Nat.factorial 576) q) : guard (integerRadicand X) L < q := by
  obtain ⟨i,j,_,s,t,e,_⟩:=h
  exact excess_past_cutoff (F.dyadic i s) (fun q hp odd low=>F.free q hp odd low i s) e

theorem point_row_of_one_prime {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L)
    (only : ∀ p q, shared F.orders (Nat.factorial 576) p → shared F.orders (Nat.factorial 576) q → p=q) :
    PointRow w := by
  refine ⟨F.u,F.v,F.values,F.pos,F.step,F.slope_large,F.rays,F.exclusions,F.roots,F.squares,?_⟩
  have pos i s : 0<F.orders i s := periodAt_positive F.values _ F.roots F.squares i s
  apply balanced_of_one_shared F.orders _ _ _ pos (Nat.factorial_pos _) F.individual _ only
  intro j i s t
  exact all_pins (pos i s) (F.dyadic i s) (fun q hp odd le=>F.free q hp odd le i s) j t

/-- Failure on an individually admissible row requires two different large primes,
each shared between different positions. Their incident pairs can differ. -/
theorem two_primes_of_no_point_row {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L)
    (bad : ¬PointRow w) :
    ∃ p q, p≠q ∧ guard (integerRadicand X) L<p ∧ guard (integerRadicand X) L<q ∧
      shared F.orders (Nat.factorial 576) p ∧ shared F.orders (Nat.factorial 576) q := by
  classical
  have ne : ¬ (∀ p q, shared F.orders (Nat.factorial 576) p → shared F.orders (Nat.factorial 576) q → p=q) :=
    fun h=>bad (point_row_of_one_prime F h)
  push Not at ne
  obtain ⟨p,q,hp,hq,diff⟩:=ne
  exact ⟨p,q,diff,F.shared_above hp,F.shared_above hq,hp,hq⟩

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.PeriodFrame.shared_above
#print axioms Sun28.PeriodWindows.point_row_of_one_prime
#print axioms Sun28.PeriodWindows.two_primes_of_no_point_row
