import OneFactor

namespace Sun28.PrimeTransfer
open Finset Filter Topology Sun28.FinitePattern Sun28.ContactFactors Sun28.SinglePrime
open Sun28.PrimeValues Sun28.ContactSieve Sun28.PrimeMass
open scoped Classical
noncomputable section

def PublishedRecurrence : Prop :=
  ∀ (c : Finset ℤ) (s : ℕ), 0 < s → 0∈c → ∃ B : ℕ, 0 < B ∧ Recurrent c s B

/-- The cyclic test is a correlation with exactly one f−g factor; the other factors
are ordinary primes in the fixed class or the same nonnegative bounded model. -/
def hasWindow (A : Fin 3→ℚ) (d K N W V s B : ℕ) (a ε : ℝ) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (b M : ℕ) (f g : ZMod n → ℝ),
    0 < V ∧ V*d*M ≤ W ∧ 2*B ≤ M ∧
    (∀ h∈coefficients A, 4*(V*d^2*h.natAbs*M^2) ≤ n) ∧
    N*W ≤ 4*V^2*d*(n*M) ∧
    (∀ x, 0≤f x ∧ f x ≤ window K b V N x) ∧
    (∀ x, 0≤g x ∧ g x ≤ a*s) ∧ 2*a*n ≤ ∑ x, g x ∧
    ∀ D ⊆ coefficients A, ∀ h∈coefficients A, h∉D →
      singleError (coefficients A) D h f g ((V*d^2:ℕ):ZMod n) M ≤ ε*((n:ℝ)*M)

/-- The modulus may depend on the required error, but is fixed before the row
number and its asymptotic scale. The model bounds and its mean are uniform. -/
def FixedClassModelInputs : Prop :=
  ∀ (A : Fin 3→ℚ) (d K : ℕ), 0<d → ∃ (a : ℝ) (s : ℕ), 0<a ∧ 0<s ∧
    ∀ (B : ℕ) (ε : ℝ), 0<ε → ∃ V : ℕ, ∃ I : ℕ, ∀ j≥I, ∃ᶠ t : ℕ in atTop,
      hasWindow A d K (lengthAt t) (rowWidth j (lengthAt t)) V s B a ε

/-- This premise concerns only the mass lost at one further fixed prime. -/
def RelativeUpperInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0<d → ∀ B : ℕ, ∃ K≥B, ∀ J : ℕ, ∃ j≥J,
      ∀ p : ℕ, p.Prime → K<p → relativeUpper (Sun28.RealPoleBounds.fixedScale n) d K j p

def gain (c : Finset ℤ) (s B : ℕ) (a : ℝ) : ℝ := a^c.card/(4*s*B^3)

theorem window_lower (A : Fin 3→ℚ) {d K N W V s B : ℕ} {a ε : ℝ} (ha : 0<a)
    (hs : 0<s) (hb : 0<B) (dp : 0<d) (grid : Recurrent (coefficients A) s B)
    (err : (coefficients A).card*ε ≤ gain (coefficients A) s B a/2)
    (win : hasWindow A d K N W V s B a ε) :
    gain (coefficients A) s B a/(2*(4*(V:ℝ)^2*d))*((N:ℝ)*W) ≤ patternMass A d K K N W := by
  obtain ⟨n,hn,b,M,f,g,vpos,wd,wide,sh,volume,fb,gb,mean,one⟩ := win
  let H : ZMod n := (V*d^2:ℕ)
  have gpos := bounded_grid_lower (coefficients A) g H ha (fun x => (gb x).1) (fun x => (gb x).2) mean le_rfl hb grid wide
  have div : (0:ℝ) < 4*s*B^3 := by positivity
  have gl : gain (coefficients A) s B a*((n:ℝ)*M) ≤ circleMass (coefficients A) g H M := by
    unfold gain
    rw [div_mul_eq_mul_div,div_le_iff₀ div]
    push_cast at gpos
    nlinarith only [gpos]
  have cmp := compare_models (coefficients A) f g H M (ε*((n:ℝ)*M)) one
  have times : 0 ≤ (n:ℝ)*M := by positivity
  have low : gain (coefficients A) s B a/2*((n:ℝ)*M) ≤ circleMass (coefficients A) f H M := by
    nlinarith only [gl,cmp,mul_le_mul_of_nonneg_right err times]
  have dom := window_le_base A vpos dp wd sh f (fun x => (fb x).1) (fun x => (fb x).2)
  have vol : (N:ℝ)*W ≤ 4*(V:ℝ)^2*d*((n:ℝ)*M) := by exact_mod_cast volume
  have gd : 0 ≤ gain (coefficients A) s B a := by unfold gain; positivity
  calc
    _ ≤ gain (coefficients A) s B a/(2*(4*(V:ℝ)^2*d))*(4*(V:ℝ)^2*d*((n:ℝ)*M)) :=
      mul_le_mul_of_nonneg_left vol (by positivity)
    _ = gain (coefficients A) s B a/2*((n:ℝ)*M) := by field_simp
    _ ≤ _ := low.trans dom

theorem hybrid_inputs_of_transfer (grid : PublishedRecurrence) (transfer : FixedClassModelInputs)
    (upper : RelativeUpperInputs) : HybridInputs := by
  apply hybrid_inputs_of_moments
  intro X c q n roots d dp bnd
  obtain ⟨K,above,up⟩ := upper X c q n roots d dp bnd
  let A := Sun28.RealPoleBounds.fixedScale n
  obtain ⟨a,s,ap,sp,model⟩ := transfer A d K dp
  obtain ⟨B,bp,recurs⟩ := grid (coefficients A) s sp (zero_coefficient A)
  let G := gain (coefficients A) s B a
  have pos : 0<G := by dsimp [G,gain]; positivity
  let e := G/(2*((coefficients A).card+1))
  have ep : 0<e := by dsimp [e]; positivity
  have err : ((coefficients A).card:ℝ)*e ≤ G/2 := by
    dsimp [e]
    have den : (0:ℝ)<2*((coefficients A).card+1) := by positivity
    rw [←mul_div_assoc,div_le_iff₀ den]
    nlinarith only [pos]
  obtain ⟨V,I,haveWindows⟩ := model B e ep
  have vp : 0<V := by
    obtain ⟨t,h⟩ := (haveWindows I le_rfl).exists
    obtain ⟨_,_,_,_,_,_,v,_⟩ := h
    exact v
  refine ⟨K,G/(2*(4*(V:ℝ)^2*d)),above,by positivity,?_⟩
  intro J
  obtain ⟨j,late,moment⟩ := up (max I J)
  have jI := (le_max_left I J).trans late
  exact ⟨j,(le_max_right I J).trans late,(haveWindows j jI).mono (fun _ w =>
    window_lower A ap sp bp dp recurs err w),moment⟩

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.window_lower
#print axioms Sun28.PrimeTransfer.hybrid_inputs_of_transfer
