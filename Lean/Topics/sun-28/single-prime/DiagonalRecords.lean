import ActualTail
import OrientedPrimes

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.NormSieve
open ManuscriptV15.Arithmetic
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- For one imaginary part the obstruction prime divides y²+1.
Each such prime allows just one class of real parts. -/
theorem diagonal_fibre (B R : ℕ) (two : 2≤R) (y : ℤ) (hy : y.natAbs≤B) (S : Finset ℤ)
    (lim : S⊆interval B) (bad : ∀ x∈S,∃ p : ℕ,p.Prime ∧ R<p ∧
      p∣adjacentNorm (x,y) true ∧ p∣adjacentNorm (x,y) false) :
    (S.card:ℚ)≤(Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1) := by
  classical
  let m := y.natAbs^2+1
  let F := fun p : ℕ => S.filter (fun x => (p:ℤ)∣x)
  let P := m.primeFactors.filter (fun p=>R<p)
  have cov : S⊆P.biUnion F := by
    intro x hx
    obtain ⟨p,pp,large,h₁,h₂⟩:=bad x hx
    let _ : Fact p.Prime:=⟨pp⟩
    have facts:= (diagonal_iff (by omega : p≠2) (x,y)).mp ⟨h₁,h₂⟩
    have xz : (x:ZMod p)=0 := facts.1
    have yz : (y:ZMod p)^2 = -1 := facts.2
    have eq : (y^2+1:ℤ).natAbs=m := by
      apply Int.natCast_inj.mp
      rw [Int.natAbs_of_nonneg (by positivity : 0≤y^2+1)]
      simp [m,sq_abs]
    have iy : (p:ℤ)∣y^2+1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; linear_combination yz)
    have pm : p∣m := by rw [←eq];exact Int.natAbs_dvd_natAbs.mpr iy
    have mp : m≠0 := by dsimp [m];omega
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp,pm,mp⟩,large⟩,
      Finset.mem_filter.mpr ⟨hx,(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp xz⟩⟩
  let size : ℚ := (2*(B:ℚ)+1)/R+1
  have per (p : ℕ) (hp : p∈P) : ((F p).card:ℚ)≤ size := by
    have h:=Finset.mem_filter.mp hp
    refine (one_class B p (Nat.prime_of_mem_primeFactors h.1).pos (F p)
      (fun x hx=>lim ((Finset.mem_filter.mp hx).1)) ?_).trans ?_
    · intro a ha b hb
      exact Int.modEq_iff_dvd.mpr (dvd_sub (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2)
    · apply add_le_add_left
      exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (by omega : 0<R)) (by exact_mod_cast h.2.le)
  have ln : P.card≤Nat.log 2 (B^2+1) := (Finset.card_filter_le ..).trans
    ((prime_divisors_card (by dsimp [m];omega : m≠0)).trans (Nat.log_mono_right (Nat.add_le_add_right (Nat.pow_le_pow_left hy 2) 1)))
  calc
    (S.card:ℚ)≤((P.biUnion F).card:ℚ) := by exact_mod_cast Finset.card_le_card cov
    _ ≤ ∑ p∈P,((F p).card:ℚ) := by exact_mod_cast Finset.card_biUnion_le (s:=P) (t:=F)
    _ ≤ ∑ _∈P,size := Finset.sum_le_sum per
    _ = (P.card:ℚ)*size := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast ln) (by dsimp [size];positivity)

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.diagonal_fibre
