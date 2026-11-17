import ActualGenerator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs

namespace ManuscriptV15.Arithmetic
open Filter
open scoped BigOperators Topology

noncomputable def ratHeight (a : ℚ) : ℝ := Real.log (max a.num.natAbs a.den : ℕ)

def marked (a : ℚ) : Prop := a=0 ∨ a=1 ∨ a=2401 ∨ a=(-343/32 : ℚ)

/-- Primitive homogeneous contact numerators at infinity, 0, 1, 2401 and -343/32. -/
def contactForms (a : ℚ) : List ℤ :=
  let u := a.num
  let v : ℤ := a.den
  [v,u,u-v,u-2401*v,32*u+343*v]

/-- Each prime occurs once, even when two valuations pass the parity test. -/
def contactPrimes (a : ℚ) : Finset ℕ :=
  let f := contactForms a
  ((f.flatMap (fun t => t.natAbs.primeFactorsList)).toFinset).filter
    (fun p => 76176 < p ∧ f.any (fun t => padicValNat p t.natAbs % 2 == 1))

theorem mem_contact_iff (a : ℚ) (p : ℕ) : p ∈ contactPrimes a ↔
    76176 < p ∧ p.Prime ∧ ∃ t ∈ contactForms a, padicValNat p t.natAbs % 2 = 1 := by
  simp only [contactPrimes, Finset.mem_filter, List.mem_toFinset, List.mem_flatMap,
    List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨t,_,ht⟩,hl,hw⟩
    exact ⟨hl,Nat.prime_of_mem_primeFactorsList ht,hw⟩
  · rintro ⟨hl,hp,t,ht,hw⟩
    have hn : padicValNat p t.natAbs ≠ 0 := by intro e; rw [e] at hw; contradiction
    have tn : t.natAbs ≠ 0 := fun e => hn (by simp [e])
    have dv : p ∣ t.natAbs := by
      by_contra h
      exact hn (padicValNat.eq_zero_iff.mpr (.inr (.inr h)))
    exact ⟨⟨t,ht,(Nat.mem_primeFactorsList_iff_dvd tn hp).mpr dv⟩,hl,t,ht,hw⟩

/-- An odd denominator valuation contributes precisely through the mark at infinity. -/
theorem infinity_contributes (a : ℚ) (p : ℕ) (big : 76176 < p) (prime : p.Prime)
    (odd : padicValNat p a.den % 2 = 1) : p ∈ contactPrimes a :=
  (mem_contact_iff ..).mpr ⟨big,prime,(a.den:ℤ),by simp [contactForms],odd⟩

def M5 (a : ℚ) : ℕ := ∏ p ∈ contactPrimes a, p
def badProduct : ℕ := ∏ p ∈ (Finset.range 76177).filter Nat.Prime, p
noncomputable def C3 : ℝ := 19 * (4608 * (210:ℝ)^300) * (badProduct:ℝ)^3 * Real.log badProduct

/-- v15:height:thm:contactheight, primary cubic bound and explicit numerical constant. -/
def FiveContact : Prop := C3 < (2:ℝ)^330770 ∧
  ∀ a : ℚ, ¬ marked a → ratHeight a ≤ C3 * (M5 a : ℝ)^3 * (1 + Real.log (M5 a))

open EllipticOrbit.Field (K P Point coordinates)

/-- Absolute logarithmic height in Q(√2), from the primitive quadratic polynomial of x.
    When x is rational, the quadratic norm polynomial has its rational root twice. -/
noncomputable def quadraticHeight (x : K) : ℝ :=
  let a : ℚ := x.re
  let b : ℚ := x.im
  let leading := Nat.lcm (2*a).den (a^2-2*b^2).den
  let conjugate₁ : ℝ := a + b * Real.sqrt 2
  let conjugate₂ : ℝ := a - b * Real.sqrt 2
  (Real.log leading + Real.log (max 1 |conjugate₁|) + Real.log (max 1 |conjugate₂|)) / 2

noncomputable def pointXHeight (T : Point) : ℝ :=
  match coordinates T with
  | none => 0
  | some (x,_) => quadraticHeight x

/-- The canonical height with the standard half-abscissa normalization. -/
def CanonicalHeightValue (T : Point) (h : ℝ) : Prop :=
  Tendsto (fun k : ℕ => pointXHeight ((2^k : ℕ) • T) / (2 * (4:ℝ)^k)) atTop (𝓝 h)

/-- v15:aggregate:thm:aggregate. Absolute height convergence and finite evaluations are
    conclusions for the same labels that occur in the two trace inequalities. -/
def AggregateTraceHeight : Prop := ∀ r : ℕ, 0 < r →
  ∃ Mplus Cplus Mprod Cprod : ℝ,
    0 < Mplus ∧ 0 ≤ Cplus ∧ 0 < Mprod ∧ 0 ≤ Cprod ∧
    ∀ n : Fin r → ℤ, (∀ i, n i ≠ 0) → ∃ x : Fin r → K, ∃ h : Fin r → ℝ,
      (∀ i, ∃ y : K, coordinates (n i • P) = some (x i,y)) ∧
      (∀ i, CanonicalHeightValue (n i • P) (h i)) ∧
      (∑ i, h i) ≤ Mplus * ratHeight (∑ i, x i).re + Cplus ∧
      ((∀ i, n i % 2 = 1) → (∑ i, h i) ≤ Mprod * ratHeight (∏ i, x i).re + Cprod)

abbrev Gaussian := ℤ × ℤ

def gaussianNorm (z : Gaussian) : ℕ := (z.1^2 + z.2^2).natAbs
def gaussianMul (z w : Gaussian) : Gaussian := (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def gaussianPrime (z : Gaussian) : Prop := gaussianNorm z > 1 ∧
  ∀ a b : Gaussian, gaussianMul a b = z → gaussianNorm a = 1 ∨ gaussianNorm b = 1
def adjacentNorm (z : Gaussian) (plus : Bool) : ℕ :=
  gaussianNorm (z.1 + (if plus then 1 else -1), z.2)
def gaussianCongruent (m : ℕ) (z w : Gaussian) : Prop :=
  Int.ModEq m z.1 w.1 ∧ Int.ModEq m z.2 w.2
def squarefree (a : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p^2 ∣ a

def gaussianPattern {k : ℕ} (c : Fin k → ℤ) (q M u w : ℕ) (p : Fin k → ℕ) : Prop :=
  q ∣ w ∧ ∃ π : Fin k → Gaussian,
    (∀ j, (p j:ℤ) = u + c j * (w:ℤ)^2 ∧ (p j).Prime ∧
      gaussianPrime (π j) ∧ gaussianNorm (π j) = p j ∧
      gaussianCongruent 16 (π j) (9,0) ∧ gaussianCongruent 7 (π j) (1,3) ∧
      gaussianCongruent M (π j) (0,1)) ∧
    (∀ j, ∀ l : ℕ, l.Prime → Odd l → ¬ (l ∣ adjacentNorm (π j) false ∧ l ∣ adjacentNorm (π j) true)) ∧
    (∀ j h, j ≠ h → ∀ e f : Bool, ∀ l : ℕ, l.Prime → Odd l →
      ¬ (l ∣ adjacentNorm (π j) e ∧ l ∣ adjacentNorm (π h) f)) ∧
    (∀ j, padicValNat 2 (adjacentNorm (π j) false) = 6 ∧ padicValNat 2 (adjacentNorm (π j) true) = 2) ∧
    (∀ j h, Nat.gcd (adjacentNorm (π j) false) (adjacentNorm (π h) true) = 4) ∧
    (∀ j e, (adjacentNorm (π j) e).Coprime (7*M))

/-- thm:v5-simultaneous-primes. Positive u,w follow every choice of the fixed inputs. -/
def GaussianTuples : Prop := ∀ k : ℕ, 2 ≤ k → ∀ c : Fin k → ℤ, Function.Injective c →
  ∀ q M : ℕ, 0 < q → 0 < M → Odd M → squarefree M → ¬ 7 ∣ M →
  ∀ H Y : ℝ, 0 < H → 0 < Y → ∃ u w : ℕ, 0 < u ∧ 0 < w ∧ H < (u:ℝ)/w^2 ∧
  ∃ p : Fin k → ℕ, gaussianPattern c q M u w p ∧ ∀ j, Y < (p j:ℝ)

/-- v15:selection:eq:count with the diagonal choice needed by v15:selection:lem:strip.
    All ray and dilation data, and the strip exponent, precede the choice of weights. -/
def GaussianCount : Prop := ∀ k : ℕ, 2 ≤ k → ∀ c : Fin k → ℤ, Function.Injective c →
  ∀ q M : ℕ, 0 < q → 0 < M → Odd M → squarefree M → ¬ 7 ∣ M →
  ∀ α : ℝ, 0 < α → α < 1/2 → ∃ c₀ C : ℝ, ∃ τ : ℝ → ℝ, 0 < c₀ ∧ 0 < C ∧
    (∀ X, 0 < τ X) ∧ Antitone τ ∧ Tendsto τ atTop (𝓝 0) ∧
    Tendsto (fun X => τ X * Real.exp ((1/2-α)*Real.log X) / (Real.log X)^k) atTop atTop ∧
    ∀ᶠ X : ℝ in atTop, let T := ⌊τ X * Real.sqrt X⌋₊
      ∃ ω : ℕ → ℕ → ℝ,
        (∀ u w, 0 ≤ ω u w ∧ ω u w ≤ C*(Real.log X)^k) ∧
        (∀ u w, ω u w ≠ 0 → X/2 ≤ (u:ℝ) ∧ (u:ℝ) ≤ X ∧ 1 ≤ w ∧ w ≤ T ∧
          ∃ p : Fin k → ℕ, gaussianPattern c q M u w p) ∧
        c₀*X*T ≤ ∑ u ∈ Finset.range (⌊X⌋₊+1), ∑ w ∈ Finset.range (T+1), ω u w

/-- For units at an odd prime, solubility at every precision describes local squareness.
    A root may be chosen afresh at each precision. -/
def localSquareAt (p a : ℕ) : Prop := ∀ k : ℕ, ∃ t : ℤ, Int.ModEq ((p:ℤ)^k) (t^2) a

def twistPointInClass (β l : ℕ) : Prop := ∃ t y : ℚ, t ≠ 0 ∧
  let x := β*t^2
  y^2 = x*(x-l)*(x+3*l)

/-- lem:original-seven-simultaneous-realization. The common multiplier is existential. -/
def SimultaneousTwists : Prop := ∀ β θ : ℕ, 0 < β → 0 < θ → squarefree β → squarefree θ →
  β.Coprime θ → β.Coprime 6 → θ.Coprime 6 → β % 24 = 17 → θ % 24 = 1 →
  (∀ p : ℕ, p.Prime → p ∣ θ → localSquareAt p β) →
  (∀ p : ℕ, p.Prime → p ∣ β → localSquareAt p θ) →
  ∃ n : ℕ, 0 < n ∧ squarefree n ∧ n.Coprime (6*θ) ∧ twistPointInClass β n ∧ twistPointInClass β (n*θ)

def pole (B : ℚ) : Prop := ∃ b : Fin 6 → ℚ, ∃ e z r₁ r₂ w : ℚ,
  let m := (1-2*b 0)*(1+b 1)*(1+2*b 2)*(1+4*b 3)*(1+6*b 4)*(1+12*b 5)
  let a := m*B
  let h := a*(a-B^2)
  B * ((∑ i, (b i^2-b i)^2) + (e*h*z*w-1)^2 + (r₁^2-a*(a-e)*(a+3*e))^2 +
    (r₂^2-a*(a*z^2-e*h)*(a*z^2+3*e*h))^2) = 0

def ratOrder (p : ℕ) (b : ℚ) : ℤ := (padicValNat p b.num.natAbs : ℤ) - padicValNat p b.den

/-- hyp:PC requires a square reduced denominator and depth four at the five listed primes. -/
def PoleCompleteness : Prop := ∀ B : ℚ, (∃ d : ℕ, B.den = d^2) → 0 < B → B < 1/2 →
  (∀ p ∈ ({2,3,5,7,13} : Finset ℕ), 4 ≤ ratOrder p B) → pole B

/-- Rational square class: b and the integer b.num*b.den differ by a rational square. -/
def locallySquareRat (p : ℕ) (b : ℚ) : Prop := b ≠ 0 ∧
  ∀ k : ℕ, ∃ t : ℤ, Int.ModEq ((p:ℤ)^k) (t^2) (b.num*b.den)

def preparedPole (b : ℚ) : Prop := ∃ e p q s : ℚ,
  let B := 17*b
  let h := e*(B-b^2)
  p^2 = B*(1-e)*(1+3*e) ∧ B*q^2 = (s^2-B*h)*(s^2+3*B*h)

/-- v15:dependencies:sec:poles, the four-witness form actually used for each prepared input. -/
def ZeroPreparation : Prop := ∀ b : ℚ, b ≠ 0 →
  (preparedPole b → ∀ p : ℕ, p.Prime → p ∉ ({2,3,17}: Finset ℕ) → ¬ (ratOrder p b < 0 ∧ Odd (ratOrder p b))) ∧
  ((∃ d : ℕ, b.den = d^2) → 0 < b → b < 17 →
    (∀ p ∈ ({2,3,17}:Finset ℕ), locallySquareRat p b) →
    3 ≤ ratOrder 2 b → 1 ≤ ratOrder 3 b → 2 ≤ ratOrder 17 b → preparedPole b)

def twist (l : ℕ) : WeierstrassCurve ℚ := ⟨0,2*l,0,-3*(l:ℚ)^2,0⟩

/-- Typed interface only. Its two arguments still require identification with the actual
    2-primary Selmer corank and the order at one of the Hasse-Weil L-function over Q. -/
def RestrictedConverse (selmerCorank₂ orderAtOne : WeierstrassCurve ℚ → WithTop ℕ) : Prop :=
  ∀ l : ℕ, 0 < l → squarefree l → l % 12 = 11 → selmerCorank₂ (twist l) = 1 → orderAtOne (twist l) = 1

end ManuscriptV15.Arithmetic
