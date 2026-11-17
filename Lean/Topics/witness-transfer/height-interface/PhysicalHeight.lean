import EllipticFrame
import Assembly

namespace WitnessTransfer.Height
open IndependentIndices IndependentIndices.Assembly
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

def detectorConstant : Nat := HeightClosure.constant [2,3,5,7,11,13,17,29,37,41,2399]
def scalarConstant : Nat := HeightClosure.constant [2,3,5,7,17]

/-- The integer bound can be the ceiling of the logarithmic height of the scaled slope. -/
structure Observed (ns : Labels) (B : Rat) where
  multiplier : Int
  primes : List Nat
  atPrime : ∀ p∈primes, Nonempty (Local.PrimeInputs p multiplier ns B)
  slopeCeiling : Nat
  fiveMark : slopeCeiling ≤ detectorConstant * (radical primes)^17 + 2

def Observed.frame {ns B} (c : Observed ns B) : Frame ns B :=
  Local.physical_frame c.primes c.atPrime

theorem observed_defects {ns B} (a b c : Observed ns B) :
    Defects (Nat.lcm (radical a.primes) (Nat.lcm (radical b.primes) (radical c.primes))) ns B ∧
    Defects (largest (radical a.primes) (radical b.primes) (radical c.primes)) ns B := by
  have ha:=Local.physical_defects a.primes a.atPrime
  have hb:=Local.physical_defects b.primes b.atPrime
  have hc:=Local.physical_defects c.primes c.atPrime
  exact ⟨lcm_defects ha (lcm_defects hb hc),three_max (P:=fun j=>Defects j ns B) ha hb hc⟩

private theorem positive_radical (ps : List Nat) (h : ∀p∈ps,0<p) : 0<radical ps := by
  induction ps with
  | nil => decide
  | cons p ps ih => exact Nat.lcm_pos (h p (by simp)) (ih fun q hq=>h q (List.mem_cons_of_mem _ hq))

private theorem Observed.positive {ns B} (c : Observed ns B) : 0<radical c.primes := by
  apply positive_radical
  intro p hp
  obtain ⟨obs⟩:=c.atPrime p hp
  have odd:=obs.odd
  omega

private theorem absorb_three {l D n : Nat} (hD : 21<D) (hn : 0<n)
    (h : 2*l^2≤15+3*(D*n+2)) : l^2<(2*D)*n := by
  have hD' : D*1≤D*n := Nat.mul_le_mul_left _ hn
  rw [Nat.mul_one] at hD'
  rw [Nat.mul_assoc]
  omega

/-- The maximum of the three *separate* slope bounds is sufficient for the abscissa step. -/
theorem comparison_height {ns B} (a b c : Observed ns B)
    (abscissas : 2*(labelSize ns)^2≤15+3*largest a.slopeCeiling b.slopeCeiling c.slopeCeiling) :
    (labelSize ns)^2<rootConstant*(observedMaximum a.frame b.frame c.frame)^17 := by
  let m:=largest (radical a.primes) (radical b.primes) (radical c.primes)
  obtain ⟨ma,mb,mc⟩:=largest_bounds (radical a.primes) (radical b.primes) (radical c.primes)
  have atMost (f : Observed ns B) (le : radical f.primes≤m) :
      f.slopeCeiling≤detectorConstant*m^17+2 :=
    Nat.le_trans f.fiveMark (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le 17)) 2)
  have combined := three_max (P:=fun k=>k≤detectorConstant*m^17+2)
    (atMost a ma) (atMost b mb) (atMost c mc)
  change (labelSize ns)^2 < (2*detectorConstant)*m^17
  apply absorb_three (by decide : 21<detectorConstant) (Nat.pow_pos (Nat.lt_of_lt_of_le a.positive ma))
  exact Nat.le_trans abscissas (Nat.add_le_add_left (Nat.mul_le_mul_left 3 combined) 15)

private theorem radical_from_growth {a c m : Nat} (large : 10000<a) (cap : c≤2^700)
    (growth : (2^(a-4))^2<c*m^17) : 2^(a/9)<m := by
  apply Nat.lt_of_not_ge
  intro small
  have limit : c*m^17≤2^(700+(a/9)*17) := by
    rw [Nat.pow_add,Nat.pow_mul]
    exact Nat.mul_le_mul cap (Nat.pow_le_pow_left small 17)
  have exponents : 700+(a/9)*17≤(a-4)*2 := by omega
  rw [←Nat.pow_mul] at growth
  exact Nat.not_lt_of_ge (Nat.le_trans limit (Nat.pow_le_pow_right (by decide) exponents)) growth

/-- Before applying the scalar height bound, the three comparisons already
    force the Lucas identity and a lower bound on one of their observed radicals. -/
theorem necessary_radical {ns B} (a b c : Observed ns B) (last_nonzero : ns.n₄≠0)
    (anchor_nonzero : ns.n₂-1≠0) (anchor : (anchorModulus:Int)∣ns.n₂-1)
    (abscissas : 2*(labelSize ns)^2≤15+3*largest a.slopeCeiling b.slopeCeiling c.slopeCeiling) :
    lucas ns.n₂ ns.n₃ ns.n₄=0 ∧ 2^(ns.n₂.natAbs/9)<largest (radical a.primes) (radical b.primes) (radical c.primes) := by
  have anchorBound:=Nat.le_of_dvd (Int.natAbs_pos.mpr anchor_nonzero) (Int.ofNat_dvd_left.mp anchor)
  have shift:=Int.natAbs_sub_le ns.n₂ 1
  rw [Int.natAbs_one] at shift
  have low : anchorModulus-1≤ns.n₂.natAbs := by omega
  have big : 10000<ns.n₂.natAbs := Nat.lt_of_lt_of_le HeightClosure.numerical_bounds.2.2.1 low
  have hs : ns.n₂.natAbs≤labelSize ns ∧ ns.n₃.natAbs≤labelSize ns ∧ ns.n₄.natAbs≤labelSize ns := by
    unfold labelSize;omega
  obtain ⟨h2,h3,h4⟩:=hs
  have bound:=comparison_height a b c abscissas
  have rootAnchor := Nat.lt_of_lt_of_le HeightClosure.numerical_bounds.1 (Nat.pow_le_pow_left (Nat.le_trans low h2) 12)
  have mag:=lucas_magnitude _ _ _ _ (by omega) h2 h3 h4
  have lc:=HeightClosure.vanish (observed_defects a b c).2.1
    (Nat.lt_of_le_of_lt mag (HeightClosure.lucas_size bound rootAnchor))
  have sep:=Nat.le_trans (exponential_size (by omega) last_nonzero lc) h3
  exact ⟨lc, radical_from_growth big (by decide : rootConstant≤2^700)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left sep 2) bound)⟩

/-- Per-contact scalar order and the integer consequence of the five-mark scalar estimate. -/
structure ScalarContacts (x : Rat) (a : Int) where
  primes : List Nat
  away : ∀p∈primes, Nat.Coprime 6 p
  atPrime : ∀p∈primes, ((p^17:Nat):Int) ∣ a-1
  fiveMark : multiplicativeHeight (SquareGate.label x) ≤ 2^(2*scalarConstant*(radical primes)^17)

private theorem coprime_radical {k : Nat} (ps : List Nat) (h : ∀p∈ps, k.Coprime p) :
    k.Coprime (radical ps) := by
  induction ps with
  | nil => exact Nat.coprime_one_right _
  | cons p ps ih =>
    exact ((h p (by simp)).mul_right (ih fun q hq=>h q (List.mem_cons_of_mem _ hq))).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)

theorem scalar_divisor {x a} (s : ScalarContacts x a) (anchor : (anchorModulus:Int)∣a-1) :
    anchorModulus*(radical s.primes)^17 ∣ (a-1).natAbs := by
  have exclude:=coprime_radical s.primes s.away
  have two : Nat.Coprime 2 (radical s.primes) := exclude.coprime_dvd_left (by decide : 2∣6)
  have three : Nat.Coprime 3 (radical s.primes) := exclude.coprime_dvd_left (by decide : 3∣6)
  have cop : Nat.Coprime anchorModulus ((radical s.primes)^17) :=
    (two.mul_left (three.pow_left 1474)).pow_right 17
  exact cop.mul_dvd_of_dvd_of_dvd (Int.ofNat_dvd_left.mp anchor)
    (Int.ofNat_dvd_left.mp (aggregate 17 (a-1) s.primes s.atPrime))

private theorem scalar_margin : 80*scalarConstant≤anchorModulus := by
  have margin:=HeightClosure.numerical_bounds.2.1
  change 80*scalarConstant*19^17<anchorModulus at margin
  have le:=Nat.mul_le_mul_left (80*scalarConstant) (by decide : 1≤19^17)
  rw [Nat.mul_one] at le
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt le margin)

private theorem scalar_exponent {A j q n : Nat} (margin : 80*j≤A) (size : A*q≤n+1) :
    34*(j*q) ≤ n-4 := by
  have h:=Nat.mul_le_mul_right q margin
  rw [Nat.mul_assoc] at h
  omega

/-- Converts scalar contact orders and the binary height bound to the exponent used in Assembly. -/
theorem scalar_height {x a} (s : ScalarContacts x a) (nonzero : a-1≠0)
    (anchor : (anchorModulus:Int)∣a-1) :
    (multiplicativeHeight (SquareGate.label x))^17 ≤ 2^(a.natAbs-4) := by
  have bound:=Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) (scalar_divisor s anchor)
  have mag:=Int.natAbs_sub_le a 1
  rw [Int.natAbs_one] at mag
  have exponent:=scalar_exponent scalar_margin (Nat.le_trans bound mag)
  calc
    _ ≤ (2^(2*scalarConstant*(radical s.primes)^17))^17 := Nat.pow_le_pow_left s.fiveMark 17
    _ = 2^(34*(scalarConstant*(radical s.primes)^17)) := by rw [← Nat.pow_mul];congr 1;grobner
    _ ≤ _ := Nat.pow_le_pow_right (by decide) exponent

/-- The four integer labels and the input label are shared throughout. The three
    observed elliptic frames may use different multiplier, prime list and local field data. -/
theorem integral_from_observations (x : Rat) (ns : Labels)
    (a b c : Observed ns (SquareGate.label x)) (s : ScalarContacts x ns.n₂)
    (odd : ns.n₁%2=1) (last_nonzero : ns.n₄≠0)
    (anchor_nonzero : ns.n₂-1≠0) (anchor : (anchorModulus:Int)∣ns.n₂-1)
    (abscissas : 2*(labelSize ns)^2≤15+3*largest a.slopeCeiling b.slopeCeiling c.slopeCeiling) :
    lucas ns.n₂ ns.n₃ ns.n₄=0 ∧ SquareGate.label x=(ns.n₁:Rat) ∧ InputRestriction.IsInteger x :=
  integral_of_frames x ns a.frame b.frame c.frame odd last_nonzero anchor_nonzero anchor
    (comparison_height a b c abscissas) (scalar_height s anchor_nonzero anchor)

#print axioms observed_defects
#print axioms comparison_height
#print axioms necessary_radical
#print axioms scalar_divisor
#print axioms scalar_height
#print axioms integral_from_observations
end WitnessTransfer.Height
