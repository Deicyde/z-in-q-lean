import PreparedDetector
import BlueprintTwists
import FiniteScalarPole
import PoleIntegerWindow
import ExactDepth

namespace Sun28.ContactFactors
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation Sun28.PreparedPoles Sun28.RealPoleBounds
open Sun28.ScalarHeight Sun28.Scalar Sun28.WitnessIndices Sun28.RealRatio Sun28.ComparisonCRT
noncomputable section

def integerRadicand (X : ℤ) : ℤ :=
  let b := 2*X^2+3
  b*(b-1)*(b-2401)*(32*b+343)*(2*b-1)

theorem cast_radicand (X : ℤ) : (integerRadicand X:ℚ)=scalarRadicand (beta X) := by
  simp [integerRadicand,scalarRadicand,beta]

theorem radicand_nonzero (X : ℤ) : integerRadicand X ≠ 0 := by
  have off:=beta_off (X:ℚ)
  rw [scalarMarks] at off
  simp only [Finset.mem_insert,Finset.mem_singleton] at off
  intro e
  have h : scalarRadicand (beta (X:ℚ))=0 := (cast_radicand X).symm.trans (by exact_mod_cast e)
  unfold scalarRadicand at h
  simp only [mul_eq_zero] at h
  rcases h with (((z|z)|z)|z)|z
  all_goals apply off
  all_goals first | exact Or.inl z | exact Or.inr (Or.inl (by linarith)) |
    exact Or.inr (Or.inr (Or.inl (by linarith))) | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))) |
    exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))

theorem signed_radicand (X : ℤ) :
    ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ δ*scalarRadicand (beta X)=((integerRadicand X).natAbs:ℚ) ∧
      δ*scalarRadicand (beta X)=|scalarRadicand (beta X)| ∧ 1≤|scalarRadicand (beta X)| := by
  rw [← cast_radicand]
  let z:=integerRadicand X
  change ∃ δ : ℚ, (δ=1 ∨ δ= -1) ∧ δ*(z:ℚ)=(z.natAbs:ℚ) ∧ δ*(z:ℚ)=|(z:ℚ)| ∧ 1≤|(z:ℚ)|
  have zn : z≠0:=radicand_nonzero X
  have absq : ((z.natAbs:ℕ):ℚ)=|(z:ℚ)| := by
    have eq:=congrArg (fun w : ℤ => (w:ℚ)) (Int.natCast_natAbs z)
    simpa only [Int.cast_natCast,Int.cast_abs] using eq
  have large : (1:ℚ)≤|(z:ℚ)| := absq ▸ (by exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr zn))
  by_cases pos : 0≤z
  · refine ⟨1,Or.inl rfl,?_,?_,large⟩ <;> simp only [one_mul,absq,abs_of_nonneg (by exact_mod_cast pos : 0≤(z:ℚ))]
  · have neg : (z:ℚ)<0 := by exact_mod_cast (lt_of_not_ge pos)
    refine ⟨-1,Or.inr rfl,?_,?_,large⟩ <;> simp only [neg_one_mul,absq,abs_of_neg neg]

def slope (A : Fin 3→ℚ) (u v : ℕ) : ℚ := (u:ℚ)/((dilation A*v:ℕ):ℚ)^2

theorem argument_eq (A : Fin 3→ℚ) (u v : ℕ) (j : Fin 3) :
    argument A u v j=A j*slope A u v := by unfold argument slope; ring

/-- Finite input to the Chinese remainder theorem for the comparison index. -/
structure Orders where
  plusOrder : ℕ
  minusOrder : ℕ
  kernelModulus : ℕ
  T : Finset ℕ
  a : ℕ→ℕ
  plus_pos : 0 < (plusOrder : ℕ)
  minus_pos : 0 < (minusOrder : ℕ)
  kernel_pos : 0 < (kernelModulus : ℕ)
  prime : ∀ p∈T, Nat.Prime p
  two : 2∈T
  common : plusOrder.gcd minusOrder=4
  dyadic_plus : padicValNat 2 plusOrder=2
  dyadic_minus : padicValNat 2 minusOrder=6
  local_avoid : ∀ p∈T,p≠2 → ¬p∣plusOrder*minusOrder
  kernel_avoid : ∀ p∈kernelModulus.primeFactors,p≠2 → ¬p∣minusOrder
  depth : ∀ p∈T,padicValNat p kernelModulus≤a p
  dyadic_depth : 6≤a 2

def Orders.accepts (o : Orders) (h : ℤ) : Prop := Congruences o.plusOrder o.minusOrder o.kernelModulus (Nat.factorial 576) o.T o.a h

theorem Orders.progression (o : Orders) : ∃ b : ℤ, ∃ L : ℕ, 0<L ∧ ∀ k : ℤ, o.accepts (b+(L:ℤ)*k) :=
  comparison_progression _ _ _ _ _ _ o.plus_pos o.minus_pos o.kernel_pos o.prime o.two o.common
    o.dyadic_plus o.dyadic_minus o.local_avoid o.kernel_avoid o.depth o.dyadic_depth
    (Nat.dvd_factorial (by decide) (by decide))

/-- Valuations required from the elliptic reductions at the finite primes.
The trace and scalar tree are evaluated on the same nine doubled inputs. -/
structure LocalEstimates (X : ℤ) (A : Fin 3→ℚ) (u v : ℕ) (values : PrimeValues A u v) (w : NinePoints) : Prop where
  trace_orders : ∀ j, let t:=argument A u v j
    let T:=ordinaryTraceAt w fixedMultiplier anchor (beta X) (A j) t
    ∀ p∈selected values j, padicValRat p T≤0
  trace_depths : ∀ j, let t:=argument A u v j
    let T:=ordinaryTraceAt w fixedMultiplier anchor (beta X) (A j) t
    ∀ p∈primes, 4≤padicValRat p (detector (A j) t/T^2)
  scalar_units : ∀ p : ℕ,p.Prime → p∈primes ∨ p∣(integerRadicand X).natAbs →
    let W:=scalarTree (scalarRadicand (beta X)) (scalarEntries w fixedMultiplier)
    W≠0 ∧ padicValRat p W=0

/-- Prime selection and finite-place estimates in the order required by Sun §6.
The first dilation precedes the roots and the uniform real bound. -/
def FiniteSelection : Prop :=
  ∀ X : ℤ, ∃ (D : ℕ) (cmin : ℤ), 0<D ∧ fixedMultiplier∣D ∧
    ∀ (c q : ℤ) (n : Fin 4→ℤ) (C : ℝ), (D:ℤ)∣c → max cmin 0<c → c=(fixedMultiplier:ℤ)*q →
      n 0=2*X^2+3 → n 1=c+1 → (∀ i,0<n i ∧ Odd (n i)) → lucas (n 1) (n 2) (n 3)=0 → 1≤C →
      let A:=fixedScale n
      ∃ (u v : ℕ) (values : PrimeValues A u v) (o : Orders), 0<v ∧
        slopeThreshold A C (1/2)<(slope A u v:ℝ) ∧
        (∀ j,∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
        ∃ (bad : Set ℤ) (hmin : ℤ), bad.Finite ∧ ∀ (h : ℤ) (B : Fin 9→AffineInput),
          o.accepts h → h∉bad → max (max anchor hmin) 0<h →
          Consequences (nineAffine B).doubles fixedMultiplier anchor ⟨q,h,n,fun i=>h*n i⟩ →
          LocalEstimates X A u v values (nineAffine B).doubles

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.cast_radicand
#print axioms Sun28.ContactFactors.radicand_nonzero
#print axioms Sun28.ContactFactors.signed_radicand
#print axioms Sun28.ContactFactors.argument_eq
#print axioms Sun28.ContactFactors.Orders.progression
