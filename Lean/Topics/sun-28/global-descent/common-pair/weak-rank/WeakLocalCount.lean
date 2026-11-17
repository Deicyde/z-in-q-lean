import WeakGaps
import OddGlobal

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.SeededPartners Sun28.GlobalSections Sun28.NormPartners
noncomputable section

theorem finite_local_labels {l : ℕ} (lp : 0<l) : (localClasses l).Finite := by
  let B : ℤ := 6*l
  have pos : 0<B := by dsimp [B];positivity
  have bounds (z : ℤ) (dvd : z∣B) : z∈Set.Icc (-B) B := by
    exact ⟨by have := Int.le_of_dvd pos (neg_dvd.mpr dvd);omega,Int.le_of_dvd pos dvd⟩
  apply ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset
  rintro ⟨a,c⟩ mem
  obtain ⟨sa,sc⟩ := Sun28.MarkedOdd.local_support_dvd lp.ne' mem
  exact ⟨bounds a sa,bounds c sc⟩

/-- Eight globally realized classes and four distinct, everywhere-locally
soluble classes with no rational lift. No finiteness theorem for Sha or
Mordell-Weil is used. -/
theorem uncancelled_local_bound {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (outside : ¬CancelledFactors b d) (hit : strictPoint b ((b*q)*d)) :
    12 ≤ (localClasses ((b*q)*d)).ncard := by
  classical
  have cop := C.coprime.coprime_dvd_right (dvd_mul_left d 6)
  have sf := Nat.squarefree_mul_iff.mpr ⟨cop,C.squarefree,ad.2.2.2.1⟩
  have r := ad.2.2.2.2.2.2.2.1
  have bb : 1<b := by omega
  have dp := ad.2.1
  have qp := C.nontrivial
  have qd : 1<q*d := by nlinarith
  let l := (b*q)*d
  have lp : 0<l := by dsimp [l];positivity
  have res : l%12=11 := C.companion_residue
  have c3 : ¬3∣l := by omega
  have sf3 : Squarefree (3*l) := Nat.squarefree_mul_iff.mpr
    ⟨(Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr c3,(by decide : Nat.Prime 3).squarefree,sf⟩
  obtain ⟨f,fi,good⟩ := rational_eight lp (candidate_strict ad C hit).2
  obtain ⟨g,gi,bad⟩ := missing_four bb qd (Nat.mul_assoc b q d) sf3 C.local_second (all_companions_fail ad outside C)
  have sub : Set.range f ∪ Set.range g ⊆ localClasses l := by
    rintro _ (⟨i,rfl⟩|⟨j,rfl⟩)
    · exact (good i).1
    · exact (bad j).1
  have dis : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,rfl⟩ ⟨j,e⟩
    exact (bad j).2 (e.symm ▸ (good i).2)
  have lower := Set.ncard_le_ncard sub (finite_local_labels lp)
  rw [Set.ncard_union_eq dis,Set.ncard_range_of_injective fi,Set.ncard_range_of_injective gi,
    Nat.card_fin,Nat.card_fin] at lower
  exact lower

theorem sixteen_of_power_of_two {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (outside : ¬CancelledFactors b d) (hit : strictPoint b ((b*q)*d))
    (power : ∃ j:ℕ, (localClasses ((b*q)*d)).ncard=2^j) :
    16 ≤ (localClasses ((b*q)*d)).ncard := by
  have low := uncancelled_local_bound ad C outside hit
  obtain ⟨j,h⟩ := power
  rw [h] at low ⊢
  have big : 4≤j := by
    by_contra! z
    interval_cases j <;> norm_num at low
  exact (Nat.pow_le_pow_right (by decide : 0<2) big : 2^4≤2^j)

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.finite_local_labels
#print axioms Sun28.WeakRank.uncancelled_local_bound
#print axioms Sun28.WeakRank.sixteen_of_power_of_two
