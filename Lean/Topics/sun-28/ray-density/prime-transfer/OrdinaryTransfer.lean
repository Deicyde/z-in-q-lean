import ClassMean
import TransferRows

namespace Sun28.PrimeTransfer
open Finset Filter Topology Sun28.SinglePrime Sun28.PrimeMass
open scoped Classical
noncomputable section

/-- Logarithmic one-prime density in a fixed interior interval, allowing removal
of the finitely many rational primes dividing any prescribed modulus V. -/
def OnePrimeDensity : Prop :=
  ∀ K : ℕ, ∃ η : ℝ, 0<η ∧ ∀ V : ℕ, 0<V → ∀ᶠ N : ℕ in atTop,
    η*N ≤ ∑ p∈band N V,classWeight K p

/-- A common bounded model for an arbitrary positive-mean weight dominated
by the ordinary W-tricked primes. No ideal class occurs in this interface. -/
def OrdinaryModelInputs : Prop :=
  ∀ (c : Finset ℤ) (d : ℕ), 0<d → 0∈c → ∃ C : ℝ, 0<C ∧
    ∀ (η : ℝ), 0<η → ∀ (ε : ℝ), 0<ε → ∀ B : ℕ,
    ∃ V : ℕ, 0<V ∧ ∃ I : ℕ, ∀ j≥I, ∀ᶠ t : ℕ in atTop,
      let N:=lengthAt t
      let W:=rowWidth j N
      let n:=N/V
      ∃ hn : 0<n, letI : NeZero n := ⟨hn.ne'⟩
        ∃ M : ℕ, V*d*M ≤ W ∧ 2*B ≤ M ∧ (∀ h∈c, 4*(V*d^2*h.natAbs*M^2) ≤ n) ∧
        N*W ≤ 4*V^2*d*(n*M) ∧ ∀ b∈units V, ∀ f : ZMod n→ℝ,
          (∀ x, 0≤f x ∧ f x ≤ (V.totient:ℝ)/V*(if (b+V*x.val).Prime then Real.log (b+V*x.val:ℕ) else 0)) →
          η*n ≤ ∑ x,f x → ∃ g : ZMod n→ℝ, (∀ x,0≤g x ∧ g x≤C) ∧ (η/2)*n ≤ ∑ x,g x ∧
          ∀ D ⊆ c, ∀ h∈c, h∉D →
            singleError c D h f g ((V*d^2:ℕ):ZMod n) M ≤ ε*((n:ℝ)*M)

theorem class_model_of_ordinary (onePrime : OnePrimeDensity) (ordinary : OrdinaryModelInputs) :
    FixedClassModelInputs := by
  intro A d K dp
  obtain ⟨η,ep,den⟩ := onePrime K
  obtain ⟨C,cp,models⟩ := ordinary (coefficients A) d dp (zero_coefficient A)
  let a:=η/4
  have ap : 0<a := by dsimp [a]; positivity
  obtain ⟨s,ss⟩ := exists_nat_gt (C/a)
  have sp : 0<s := by
    have : (0:ℝ)<s := (div_pos cp ap).trans ss
    exact_mod_cast this
  have cb : C ≤ a*s := by
    have := (div_lt_iff₀ ap).mp ss
    linarith
  refine ⟨a,s,ap,sp,?_⟩
  intro B ε epos
  obtain ⟨V,vp,I,run⟩ := models η ep ε epos B
  refine ⟨V,I,?_⟩
  intro j large
  apply Filter.Eventually.frequently
  filter_upwards [run j large,length_grows.eventually (den V vp),length_grows.eventually (eventually_ge_atTop (64*V))] with t spec mass room
  let N:=lengthAt t
  let W:=rowWidth j N
  let n:=N/V
  obtain ⟨hn,M,width,wide,short,vol,select⟩:=spec
  let _ : NeZero n:=⟨hn.ne'⟩
  obtain ⟨b,hb,density⟩ := exists_dense_class K N V vp room ep mass
  let f (x:ZMod n) := ((V.totient:ℝ)/V)*window K b V N x
  have rate : (0:ℝ)≤V.totient/V ∧ (V.totient:ℝ)/V ≤ 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one (by exact_mod_cast vp)]
    exact_mod_cast Nat.totient_le V
  have win (x : ZMod n) : 0≤window K b V N x := by
    unfold window;split
    next => exact (class_weight_le _ _).1
    next => rfl
  have fb (x : ZMod n) : 0≤ f x ∧ f x ≤ window K b V N x :=
    ⟨mul_nonneg rate.1 (win x),mul_le_of_le_one_left (win x) rate.2⟩
  have maj (x : ZMod n) : f x ≤ (V.totient:ℝ)/V*(if (b+V*x.val).Prime then Real.log (b+V*x.val:ℕ) else 0) := by
    apply mul_le_mul_of_nonneg_left _ rate.1
    let p := b+V*x.val
    have pp : (0:ℝ)≤(if p.Prime then Real.log (p:ℝ) else 0) := by
      split
      next h => exact Real.log_nonneg (by exact_mod_cast h.one_le)
      next => rfl
    change window K b V N x ≤ if p.Prime then Real.log (p:ℝ) else 0
    unfold window
    split
    next =>
      change classWeight K p ≤ _
      by_cases ok : oneClass K p
      · simp [classWeight,ok,ok.1]
      · simpa [classWeight,ok] using pp
    next => exact pp
  obtain ⟨g,gb,mean,errs⟩ := select b hb f (fun x=>⟨(fb x).1,maj x⟩) density
  refine ⟨n,⟨hn.ne'⟩,b,M,f,g,vp,width,wide,short,vol,fb,fun x=>⟨(gb x).1,(gb x).2.trans cb⟩,?_,errs⟩
  rw [show 2*a=η/2 by dsimp [a]; ring]
  exact mean

/-- For the lower base count the arithmetic restriction has become a
one-variable prime density. The new-prime collision estimates stay separate. -/
theorem hybrid_of_ordinary (grid : PublishedRecurrence) (onePrime : OnePrimeDensity)
    (ordinary : OrdinaryModelInputs) (upper : RelativeUpperInputs) : HybridInputs :=
  hybrid_inputs_of_transfer grid (class_model_of_ordinary onePrime ordinary) upper

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.class_model_of_ordinary
#print axioms Sun28.PrimeTransfer.hybrid_of_ordinary
