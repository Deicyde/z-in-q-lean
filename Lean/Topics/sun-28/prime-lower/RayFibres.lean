import CommonPrimes

namespace Sun28.PrimeLower
open Finset Sun28.MixedSieve Sun28.FinitePattern
open scoped Classical
noncomputable section

/-- After the base unit is fixed, lift choices lie on independent prescribed norm circles.
The numerator contains the two distinguished base classes. The denominator contains every
base commutator class and the entire norm kernel. -/
def rayProportion {I : Type*} [Fintype I] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (t : (i:I) → ZMod (q i)) (G C : Type*) [Fintype G] [Fintype C] : ℝ :=
  (Fintype.card (C × ((i : I) → {z : Circle (q i) (t i) // z ∉ bad (q i) (t i) true})) : ℝ) /
  Fintype.card (G × ((i : I) → Circle (q i) 1))

/-- A change of finite presentation is sufficient to use the normalized ray estimate
for an actual Artin fibre. No independence or analytic density assumption is made here. -/
theorem ray_fraction {I : Type*} [Fintype I] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (t : (i:I) → ZMod (q i)) (nz : ∀ i,t i ≠ 0)
    (G C : Type*) [Fintype G] [Fintype C] :
    rayProportion q t G C = (Fintype.card C : ℝ)/Fintype.card G *
      ∏ i, ((bad (q i) (t i) true)ᶜ.card:ℝ)/Fintype.card (Circle (q i) (t i)) := by
  classical
  have num (i : I) : Fintype.card {z : Circle (q i) (t i) // z ∉ bad (q i) (t i) true} =
      (bad (q i) (t i) true)ᶜ.card := by
    simp [Fintype.card_subtype_compl,Fintype.card_coe,Finset.card_compl]
  have den (i : I) : Fintype.card (Circle (q i) 1)=Fintype.card (Circle (q i) (t i)) :=
    Fintype.card_congr (rotate (nz i))
  unfold rayProportion
  simp only [Fintype.card_prod,Fintype.card_pi,num,den,Nat.cast_mul,Nat.cast_prod]
  rw [Finset.prod_div_distrib]
  ring

theorem ray_fraction_lower {I : Type*} [Fintype I] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (t : (i:I) → ZMod (q i)) (nz : ∀ i,t i ≠ 0) (large : ∀ i, 7≤q i)
    (G C : Type*) [Fintype G] [Fintype C] :
    (Fintype.card C : ℝ)/Fintype.card G * (∏ i, atom (q i)) ≤ rayProportion q t G C := by
  rw [ray_fraction q t nz G C]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply prod_le_prod₀
  · intro i _
    have hi : (7:ℝ)≤q i := by exact_mod_cast large i
    dsimp [atom]
    exact sub_nonneg.mpr ((div_le_iff₀ (by linarith)).mpr (by linarith))
  · exact fun i _ => one_fibre (large i) (nz i)

/-- Finite group form of Hilbert 90. For *any* Gaussian unit z of norm one modulo an
odd prime there exists a unit a such that a = z conjugate(a), even in the split case. -/
theorem norm_one_commutator {p : ℕ} [Fact p.Prime] (odd : p≠2)
    (z : Circle p 1) : ∃ x y : ZMod p, x^2+y^2≠0 ∧
       x=z.val.1*x+z.val.2*y ∧ y=z.val.2*x-z.val.1*y := by
  have two : (2:ZMod p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun h => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
  have rel:=z.property
  by_cases neg : z.val.1= -1
  · rw [neg] at rel
    have yz : z.val.2=0 := by
      have sq : z.val.2^2=0 := by linear_combination rel
      simpa using sq
    exact ⟨0,1,by simp,by simp [yz],by simp [neg]⟩
  · refine ⟨1+z.val.1,z.val.2,?_,?_,?_⟩
    · have eq : (1+z.val.1)^2+z.val.2^2 = 2*(1+z.val.1) := by linear_combination rel
      rw [eq]
      apply mul_ne_zero two
      intro h
      apply neg
      linear_combination h
    · linear_combination -rel
    · ring

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.ray_fraction
#print axioms Sun28.PrimeLower.ray_fraction_lower
#print axioms Sun28.PrimeLower.norm_one_commutator
