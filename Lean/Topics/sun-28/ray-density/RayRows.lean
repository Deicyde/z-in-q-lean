import RaySections

namespace Sun28.RayDensity
open Finset
noncomputable section

variable {P : Finset ℕ}
abbrev NormRow (P : Finset ℕ) := (p:↥P)→(ZMod p.val)ˣ

/-- One eligible ray above each of the two conjugate base classes, with the actual
small and varying norm fibres. The second modulus-7 class is already oriented by conjugation. -/
def eligible (P : Finset ℕ) (t : NormRow P) :=
  ↥baseRays × allowedFibre 3 1 × allowedFibre 5 1 × ((p:↥P)→allowedFibre p.val (t p))
def total (P : Finset ℕ) (t : NormRow P) :=
  ↥baseCoset × normFibre 3 1 × normFibre 5 1 × ((p:↥P)→normFibre p.val (t p))

def fraction (P : Finset ℕ) (t : NormRow P) : ℝ :=
    (Nat.card (eligible P t):ℝ)/Nat.card (total P t)

/-- The factor 1/64 includes the two surviving lifts on the norm-one fibres at 3 and 5. -/
theorem exact_fraction (t : NormRow P) :
    fraction P t=(1/64)*∏ p:↥P,survival p.val (t p) := by
  classical
  have h₁ : Nat.card ↥baseRays=2 := by rw [Nat.card_eq_finsetCard];exact base_coset_fraction.2.1
  have h₂ : Nat.card ↥baseCoset=32 := by rw [Nat.card_eq_finsetCard];exact base_coset_fraction.2.2
  have es : fraction P t=((2:ℝ)/32)*survival 3 1*survival 5 1*∏ p:↥P,survival p.val (t p) := by
    unfold fraction eligible total survival
    simp only [Nat.card_prod,Nat.card_pi,Nat.cast_mul,Nat.cast_prod,h₁,h₂,Finset.prod_div_distrib]
    norm_num
    ring
  rw [es,small_fibres.1,small_fibres.2]
  ring

/-- All positions in a row can have different unit norms at every new prime. -/
theorem k_row_fibres {L k : ℕ} (large : 2≤L)
    (primes : ∀ p∈P,p.Prime ∧ 11≤p ∧ p≤L) (t : Fin k → NormRow P) :
    (Real.exp (-48)/(64*(2*(1+4*Real.log L))^4))^k ≤ ∏ j:Fin k, fraction P (t j) := by
  let _ (p : ↥P) : Fact p.val.Prime := ⟨(primes _ p.property).1⟩
  have lp := Real.log_nonneg (by exact_mod_cast (show 1≤L by omega) : 1≤(L:ℝ))
  have den : 0 < (2*(1+4*Real.log (L:ℝ)))^4 := by positivity
  have per (j : Fin k) :
      Real.exp (-48)/(64*(2*(1+4*Real.log L))^4) ≤ fraction P (t j) := by
    rw [exact_fraction]
    have lo: ∏ p∈P,both p ≤ ∏ p:↥P,survival p.val (t j p) := by
      rw [←prod_attach P both]
      apply prod_le_prod₀
      · intro p _;exact (local_logs (primes p.val p.property).2.1).1.le
      · intro p _;exact survival_lower (by have := (primes p.val p.property).2.1;omega) _
    have bound:=(two_sign_product large P primes).trans lo
    calc _ = ((1:ℝ)/64)*(Real.exp (-48)/(2*(1+4*Real.log L))^4) := by
              rw [div_eq_mul_inv, mul_inv_rev];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left bound (by norm_num)
  calc _ = ∏ _j:Fin k,Real.exp (-48)/(64*(2*(1+4*Real.log L))^4) := by simp [div_pow]
       _ ≤ _ := prod_le_prod₀ (fun _ _=>by positivity) (fun j _=>per j)

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.exact_fraction
#print axioms Sun28.RayDensity.k_row_fibres
