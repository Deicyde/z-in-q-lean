import WeakLocalCount

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.SeededPartners Sun28.PreparedPoles Sun28.GlobalSections Sun28.NormPartners
noncomputable section
set_option maxRecDepth 8000

private theorem square_at_prime {p a : ℕ} (hp : p.Prime) (odd : p≠2) (unit : (a:ZMod p)≠0)
    (sq : IsSquare (a:ZMod p)) : LocalSquareAt p a := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact local_square_of_legendre odd ((legendreSym.eq_one_iff' p unit).mpr sq)

theorem admissible_17_457 : AdmissiblePair 17 457 := by
  have p17 : Nat.Prime 17 := by norm_num
  have p457 : Nat.Prime 457 := by norm_num
  refine ⟨by decide,by decide,p17.squarefree,p457.squarefree,by decide,by decide,by decide,by decide,by decide,?_,?_⟩
  · intro p pp pd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq pp p457).mp pd
    exact square_at_prime p457 (by decide) (by decide) ⟨336,by decide⟩
  · intro p pp pb
    obtain rfl := (Nat.prime_dvd_prime_iff_eq pp p17).mp pb
    exact square_at_prime p17 (by decide) (by decide) ⟨7,by decide⟩

theorem seeded_weak_17_457 : Candidate 17 457 19 ∧ strictPoint 17 ((17*19)*457) := by
  have prime : Nat.Prime 17 := by norm_num
  have other : Nat.Prime 19 := by norm_num
  have sf : Squarefree (17*19:ℕ) := Nat.squarefree_mul_iff.mpr ⟨by decide,prime.squarefree,other.squarefree⟩
  have first : Family 17 19 := ⟨75/67,185744/(19*67^2),by norm_num,by norm_num⟩
  have at_b (p:ℕ) (pp:p.Prime) (dp:p∣17) : IsSquare ((19:ℕ):ZMod p) := by
    obtain rfl := (Nat.prime_dvd_prime_iff_eq pp prime).mp dp
    exact ⟨6,by decide⟩
  have at_q (p:ℕ) (pp:p.Prime) (dp:p∣19) : IsSquare ((17:ℕ):ZMod p) := by
    obtain rfl := (Nat.prime_dvd_prime_iff_eq pp other).mp dp
    exact ⟨6,by decide⟩
  exact ⟨⟨by decide,sf,by decide,by decide,by decide,cover_of_family (by decide) (by decide) sf first,
    partner_local admissible_17_457 (by decide) (by decide) at_b at_q⟩,
    457/4,6699667071/64,by norm_num,by norm_num,by norm_num⟩

/-- This exact seeded triple meets the nonzero simultaneous-point conclusion. -/
theorem seeded_pair_points : Sun28.PrescribedPoints.NonzeroPair (17:ℚ) (457:ℚ) := by
  obtain ⟨C,H⟩ := seeded_weak_17_457
  obtain ⟨u,y,un,yn,e⟩ := strict_of_family (b:=17) (d:=19) (by decide) (by decide)
    (by norm_num : Nat.Prime 19).squarefree (candidate_quartics admissible_17_457 C).1
  obtain ⟨v,z,vn,zn,h⟩ := H
  exact ⟨323,u,v,y,z,by norm_num,un,vn,yn,zn,e,by norm_num at h ⊢;exact h⟩

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.admissible_17_457
#print axioms Sun28.WeakRank.seeded_weak_17_457
#print axioms Sun28.WeakRank.seeded_pair_points
