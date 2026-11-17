import TYZTraceCoefficient

/-! Theorem 1.1 for the class-three cofactors, the printed row and the rank conclusion. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq

/-- A distinguished factor of class three, and an unordered set of factors of class one. -/
def thirdFactors (m : ℕ) : Finset (ℕ × Finset ℕ) :=
  (m.divisors ×ˢ m.divisors.powerset).filter fun p => p.1%8=3 ∧
    (∀ r ∈ p.2, 1 < r ∧ r%8=1) ∧ p.1 * (∏ r ∈ p.2, r) = m

private theorem mem_thirdFactors {m b : ℕ} (hm : 0 < m) (R : Finset ℕ) : (b,R) ∈ thirdFactors m ↔
    b%8=3 ∧ (∀ r ∈ R, 1 < r ∧ r%8=1) ∧ b * (∏ r ∈ R, r) = m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · rintro ⟨hb,hR,hm'⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_,hm.ne'⟩,
      Finset.mem_powerset.mpr ?_⟩,hb,hR,hm'⟩
    · exact ⟨_,hm'.symm⟩
    · intro r hr
      apply Nat.mem_divisors.mpr
      refine ⟨(Finset.dvd_prod_of_mem id hr).trans ?_,hm.ne'⟩
      rw [←hm']
      exact dvd_mul_left _ _

/-- The right-hand side of TYZ Theorem 1.1 specialized to m ≡ 3 modulo 8. -/
def thirdSum (m : ℕ) : ℕ := ∑ p ∈ thirdFactors m, genusNumber p.1 * ∏ r ∈ p.2, genusNumber r

private abbrev Sevens (n : ℕ) := ↥(n.divisors.filter fun e => e%8=7)
private abbrev Splits (n : ℕ) := (e : Sevens n) × ↥(thirdFactors (n/e.val))

private def splitTerm {n : ℕ} (hd : n%8=5) (T : BracketTerm n) : Splits n := by
  have h0 := T.d₀mod
  have he : T.d₀ ∣ n := ⟨_,by rw [←Nat.mul_assoc]; exact T.product.symm⟩
  let e : Sevens n := ⟨T.d₀,Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨he,by omega⟩,h0⟩⟩
  have hm : n/T.d₀ = T.d₁ * (∏ r ∈ T.rest, r) := by
    have eq := congrArg (fun k : ℕ => k / T.d₀) T.product.symm
    exact eq.trans (by rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < T.d₀)])
  have hmpos : 0 < n/T.d₀ := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd he) (by omega)
  exact ⟨e,⟨(T.d₁,T.rest),(mem_thirdFactors hmpos T.rest).mpr ⟨T.second_mod hd,T.rest_factors,hm.symm⟩⟩⟩

private def joinTerm {n : ℕ} (p : Splits n) : BracketTerm n := by
  obtain ⟨hdiv,h7⟩ := Finset.mem_filter.mp p.1.property
  obtain ⟨he,hn⟩ := Nat.mem_divisors.mp hdiv
  have hm := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd he) (Nat.pos_of_ne_zero hn)
  obtain ⟨h3,hR,hprod⟩ := (mem_thirdFactors (b := p.2.val.1) hm p.2.val.2).mp p.2.property
  refine ⟨p.1.val,p.2.val.1,p.2.val.2,h7,Or.inr h3,by omega,hR,?_⟩
  rw [Nat.mul_assoc,hprod,Nat.mul_comm,Nat.div_mul_cancel he]

/-- Marking the unique class-seven factor is bijective, including decompositions with no class-one factors. -/
private def splitEquiv (n : ℕ) (hn : n%8=5) : BracketTerm n ≃ Splits n where
  toFun := splitTerm hn
  invFun := joinTerm
  left_inv T := BracketTerm.ext rfl rfl rfl
  right_inv p := by rcases p with ⟨⟨e,h⟩,⟨⟨b,R⟩,k⟩⟩; rfl

set_option maxHeartbeats 800000 in
/-- Exact natural-number equality before reduction modulo two. -/
theorem printedCoefficient_split {n : ℕ} (hn : n%8=5) : printedCoefficient n hn =
    ∑ e ∈ n.divisors.filter (fun e => e%8=7), genusNumber e * thirdSum (n/e) := by
  let _ : Fintype (BracketTerm n) := Fintype.ofEquiv _ (bracketEquiv n hn).symm
  let F (p : Splits n) := genusNumber p.1.val * (genusNumber p.2.val.1 * ∏ r ∈ p.2.val.2, genusNumber r)
  calc printedCoefficient n hn = ∑ T : BracketTerm n, F (splitEquiv n hn T) := by
         unfold printedCoefficient
         exact Finset.sum_congr rfl fun T _ => Nat.mul_assoc _ _ _
       _ = ∑ p : Splits n, F p := (splitEquiv n hn).sum_comp F
       _ = ∑ e : Sevens n, ∑ t : ↥(thirdFactors (n/e.val)), F ⟨e,t⟩ := Fintype.sum_sigma _
       _ = ∑ e : Sevens n, genusNumber e.val * thirdSum (n/e.val) := by
         apply Finset.sum_congr rfl
         intro e _
         unfold F thirdSum
         rw [Finset.mul_sum]
         exact Finset.sum_coe_sort (thirdFactors (n/e.val)) (fun q => genusNumber e.val *
           (genusNumber q.1 * ∏ r ∈ q.2, genusNumber r))
       _ = _ := Finset.sum_coe_sort (n.divisors.filter (fun e => e%8=7)) (fun e => genusNumber e * thirdSum (n/e))

/-- TYZ Theorem 1.1 is needed only on the nontrivial squarefree residue-three cofactors. -/
def ClassThreePeriods (L : ℕ → ℤ) : Prop :=
  ∀ m, Squarefree m → m%8=3 → (L m : ZMod 2) = (thirdSum m : ZMod 2)

private theorem seven_cofactor {n e : ℕ} (hn : n%8=5) (he : e ∣ n) (h7 : e%8=7) : (n/e)%8=3 := by
  have eq : ((n/e)%8*(e%8))%8 = n%8 := (Nat.mul_mod _ _ _).symm.trans (congrArg (·%8) (Nat.div_mul_cancel he))
  have := Nat.mod_lt (n/e) (by decide : 0 < 8)
  rw [h7,hn] at eq
  omega

theorem row_coefficient {L : ℕ → ℤ} (h1 : L 1 = 1) (hc : ClassThreePeriods L)
    {n : ℕ} (hs : Squarefree n) (hn : n%8=5) : (traceCoefficient L n : ZMod 2) = ZInQ.RouteK.Rank5b.T5bCl n := by
  rw [coefficient_mod_two L h1 hs (Or.inl hn),←printedCoefficient_mod_two hn hs,printedCoefficient_split hn,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨he,h7⟩ := Finset.mem_filter.mp he
  have hdiv := (Nat.mem_divisors.mp he).1
  rw [hc _ (hs.squarefree_of_dvd (Nat.div_dvd_of_dvd hdiv)) (seven_cofactor hn hdiv h7),Nat.cast_mul,mul_comm]

/-- A point with the computed odd coefficient yields the anti-invariant point required for positive rank. -/
theorem antiPoint_of_genusTraces {D : RecursionData} {n : ℕ} (hn : n%8=5) (hs : Squarefree n)
    {σ : Gal} (H : LocalTraceLaw D σ n) (h1 : D.L 1 = 1) (hc : ClassThreePeriods D.L)
    (hT : ∀ m : ℕ, 0 < m → m • representative D n = 0 →
      representative D n ∈ pointsOver (Rank.imaginaryField 1) ∧ (4:ℕ) • representative D n = 0)
    (hM : GaloisMinus n (tyzIsogeny ((2:ℕ) • representative D n)))
    (hOdd : ZInQ.RouteK.Rank5b.T5bCl n = 1) : Rank.AntiPoint n := by
  have hb := (row_coefficient h1 hc hs hn).trans hOdd
  have hodd : Odd (traceCoefficient D.L n) := by
    by_contra hz
    have hEven : Even (traceCoefficient D.L n) := Int.not_odd_iff_even.mp hz
    exact zero_ne_one (hEven.intCast_zmod_two.symm.trans hb)
  have hinf := infinite_of_odd H (Or.inl hn) hT hodd
  have hImage := Rank.image_double_infinite tyzIsogeny tyzIsogeny_kernel_two _ hinf
  obtain (hz | ⟨u,v,hp,he⟩) := (minus_iff_coordinates (by omega : 0 < n) _).mp hM
  · exact False.elim (hImage 1 (by decide) (by simpa using hz))
  · rw [←he] at hImage
    exact ⟨u,v,hp,hImage⟩

/-- One common system of modular images and conjugates. For each squarefree input the only
pointwise geometric inputs are the raw genus trace formulas, its torsion bound, and minus descent. -/
theorem publicRank_of_genusTraces (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L)
    (h : ∀ n, n%8=5 → Squarefree n → ∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n ∧
      (∀ m : ℕ, 0 < m → m • representative (S.recursion L eps) n = 0 →
        representative (S.recursion L eps) n ∈ pointsOver (Rank.imaginaryField 1) ∧
        (4:ℕ) • representative (S.recursion L eps) n = 0) ∧
      GaloisMinus n (tyzIsogeny ((2:ℕ) • representative (S.recursion L eps) n))) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply PublicRankJoin.certifiedRank_of_oddClassSumToAntiPoint
  intro n hn hs hOdd
  obtain ⟨σ,H,hT,hM⟩ := h n hn hs
  exact antiPoint_of_genusTraces hn hs H h1 hc hT hM hOdd

/-- The literal compositum supplies the pointwise torsion hypothesis by membership of
the recursively constructed integral point. -/
theorem publicRank_of_compositumTraces (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (h1 : L 1 = 1) (hc : ClassThreePeriods L) (fields : TraceFields (S.recursion L eps) S.extended)
    (hT : ∀ n, n%8=5 → Squarefree n → ∀ Y : pointsOver (genusCompositum S.extended n),
      ∀ m : ℕ, 0 < m → m • Y.val = 0 →
        Y.val ∈ pointsOver (Rank.imaginaryField 1) ∧ (4:ℕ) • Y.val = 0)
    (h : ∀ n, n%8=5 → Squarefree n → ∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n ∧
      GaloisMinus n (tyzIsogeny ((2:ℕ) • representative (S.recursion L eps) n))) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply publicRank_of_genusTraces S L eps h1 hc
  intro n hn hs
  obtain ⟨σ,H,hM⟩ := h n hn hs
  exact ⟨σ,H,hT n hn hs ⟨_,representative_mem fields n hs (Or.inl hn)⟩,hM⟩

#print axioms printedCoefficient_split
#print axioms row_coefficient
#print axioms antiPoint_of_genusTraces
#print axioms publicRank_of_genusTraces
#print axioms publicRank_of_compositumTraces
end
end ZInQBlueprint.TYZ.Specialization.TraceAction
