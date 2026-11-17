import ScalarPrimeSupport
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

private theorem flip {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (pq : p%4=3) (qq : q%4=3)
    (u : ℤ) (red : (p:ℤ)%(q:ℤ)=u) : legendreSym p q = -legendreSym q u := by
  rw [legendreSym.quadratic_reciprocity_three_mod_four qq pq,legendreSym.mod q p,red]

/-- A concrete reduced progression whose primes divide no scalar squareclass. -/
theorem progression_excluded (x : ℚ) (p : ℕ) (pp : p.Prime) (r : p%12632664=10304207) :
    ¬p∣(scalarClass x).natAbs := by
  let _ : Fact p.Prime := ⟨pp⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 109) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 439) := ⟨by decide⟩
  have p2 : p≠2 := by omega
  have p4 : p%4=3 := by omega
  have op : 2<p := by omega
  have red (q k : ℕ) (h : p%q=k) : (p:ℤ)%(q:ℤ)=k := by exact_mod_cast h
  have minusOne : legendreSym p (-1) = -1 := by
    apply (legendreSym.eq_neg_one_iff p).mpr
    simpa only [Int.cast_neg,Int.cast_one] using
      (show ¬IsSquare (-1:ZMod p) by rw [ZMod.exists_sq_eq_neg_one_iff]; omega)
  have negsmall (q : ℕ) [Fact q.Prime] (m : q%4=3) :
      legendreSym q ((q-1:ℕ):ℤ) = -1 := by
    have q0 := (Fact.out : q.Prime).pos
    rw [show ((q-1:ℕ):ℤ)=(q:ℤ)-1 by omega]
    apply (legendreSym.eq_neg_one_iff q).mpr
    simp only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_self,Int.cast_one,zero_sub]
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have two : legendreSym p 2 = 1 := by
    have nz : (2:ZMod p)≠0 := by
      intro z
      have e := (ZMod.natCast_eq_zero_iff (2:ℕ) p).mp (by simpa using z)
      exact (not_le_of_gt op) (Nat.le_of_dvd (by decide) e)
    apply (legendreSym.eq_one_iff' p nz).mpr
    exact (ZMod.exists_sq_eq_two_iff p2).mpr (Or.inr (by omega))
  have three : legendreSym p 3 = 1 := by
    have eq := flip (q:=3) p4 (by decide) 2 (red 3 2 (by omega))
    rw [show (2:ℤ)=((3-1:ℕ):ℤ) by decide,negsmall 3 (by decide)] at eq
    exact eq.trans (by norm_num)
  have eleven : legendreSym p 11 = -1 := by
    simpa using (flip (q:=11) p4 (by decide) 1 (red 11 1 (by omega)))
  have hundred : legendreSym p 109 = 1 := by
    change legendreSym p ((109:ℕ):ℤ)=1
    rw [legendreSym.quadratic_reciprocity_one_mod_four (p:=109) (by decide) p2,
      legendreSym.mod 109 p,red 109 1 (by omega)]
    exact legendreSym.at_one 109
  have last : legendreSym p 439 = 1 := by
    have eq := flip (q:=439) p4 (by decide) 438 (red 439 438 (by omega))
    rw [show (438:ℤ)=((439-1:ℕ):ℤ) by decide,negsmall 439 (by decide)] at eq
    exact eq.trans (by norm_num)
  have a : legendreSym p (-6)= -1 := by
    rw [show (-6:ℤ)=(-1)*2*3 by decide,legendreSym.mul,legendreSym.mul,minusOne,two,three];decide
  have b : legendreSym p 1199= -1 := by
    rw [show (1199:ℤ)=11*109 by decide,legendreSym.mul,eleven,hundred];decide
  have c : legendreSym p (-439)= -1 := by
    rw [show (-439:ℤ)=(-1)*439 by decide,legendreSym.mul,minusOne,last];decide
  intro pd
  obtain ⟨sf,y,live,curve⟩:=octic_twist x
  have options:=splitting_at_prime sf live curve pp op pd
  have f₁ := (legendreSym.eq_neg_one_iff p).mp a
  have f₂ := (legendreSym.eq_neg_one_iff p).mp minusOne
  have f₃ := (legendreSym.eq_neg_one_iff p).mp b
  have f₄ := (legendreSym.eq_neg_one_iff p).mp c
  push_cast at f₁ f₂ f₃ f₄
  tauto

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.progression_excluded

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight Finset

noncomputable def representedResidues (Q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range Q).filter (fun a => ∃ x : ℚ, (scalarClass x).natAbs%Q=a)

/-- For any finite set of forbidden primes all attained residues lie in the reduced residues. -/
theorem finite_residue_bound (S : Finset ℕ)
    (hs : ∀ p∈S, p.Prime ∧ p%12632664=10304207) :
    let Q := S.prod id
    (representedResidues Q).card ≤ Q.totient := by
  classical
  dsimp only
  let Q := S.prod id
  change (representedResidues Q).card ≤ Q.totient
  unfold representedResidues
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨lt,x,rfl⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨lt,?_⟩
  have co : Q.Coprime (scalarClass x).natAbs := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (Nat.Prime.coprime_iff_not_dvd (hs p hp).1).mpr (progression_excluded x p (hs p hp).1 (hs p hp).2)
  change Nat.gcd Q ((scalarClass x).natAbs%Q)=1
  calc
    _ = Nat.gcd ((scalarClass x).natAbs%Q) Q := Nat.gcd_comm ..
    _ = Nat.gcd Q (scalarClass x).natAbs := (Nat.gcd_rec Q (scalarClass x).natAbs).symm
    _ = 1 := co

theorem finite_density_bound (S : Finset ℕ) (hs : ∀ p∈S, p.Prime ∧ p%12632664=10304207) :
    let Q := S.prod id
    ((representedResidues Q).card:ℚ) / Q ≤
      ∏ p∈S, (1-(p:ℚ)⁻¹) := by
  classical
  dsimp only
  let Q := S.prod id
  have qpos : 0 < Q := Finset.prod_pos fun p hp => (hs p hp).1.pos
  have pos : (0:ℚ)<Q := by exact_mod_cast qpos
  apply (div_le_iff₀ pos).mpr
  have bound := finite_residue_bound S hs
  have val := Nat.totient_eq_mul_prod_factors Q
  have same : Q.primeFactors=S := by
    exact Nat.primeFactors_prod fun p hp => (hs p hp).1
  rw [same,mul_comm] at val
  exact (show _ ≤ (Q.totient:ℚ) by exact_mod_cast bound).trans val.le

end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.finite_residue_bound
#print axioms Sun28.ScalarQuotients.finite_density_bound
