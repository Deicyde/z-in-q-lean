import PeriodNarrow
import NormCollision

namespace Sun28.PeriodWindows
open ManuscriptV15.Arithmetic Sun28.NormSieve Sun28.GaussianSelection Finset
open scoped Classical
noncomputable section

/-- Rational primes in a fixed primitive Gaussian ray; generator conditions
are literal congruences at every odd guard prime. -/
def rayGenerator (K : ℕ) (z : Gaussian) : Prop :=
  gaussianCongruent 16 z (9,0) ∧ gaussianCongruent 7 z (1,3) ∧
    ∀ q, q.Prime → q≠2 → q≠7 → q≤K → gaussianCongruent q z (0,1)

def primeBase (K N : ℕ) : Finset ℕ :=
  (range (N+1)).filter (fun p=>p.Prime ∧ ∃ z, gaussianNorm z=p ∧ rayGenerator K z)

theorem finite_guard_free {K : ℕ} {z : Gaussian} (ray : rayGenerator K z)
    {q : ℕ} (prime : q.Prime) (odd : q≠2) (le : q≤K) (s : Bool) : ¬q∣adjacentNorm z s := by
  intro d
  by_cases seven:q=7
  · subst q
    have zd : (adjacentNorm z s:ℤ) ≡ 0 [ZMOD 7] :=
      Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr d)
    have sv:=ray_seven ray.2.1
    cases s
    · exact (by decide : ¬(2:ℤ) ≡ 0 [ZMOD 7]) (sv.2.symm.trans zd)
    · exact (by decide : ¬(6:ℤ) ≡ 0 [ZMOD 7]) (sv.1.symm.trans zd)
  · let _ : Fact q.Prime := ⟨prime⟩
    obtain ⟨rr,ii⟩:=ray.2.2 q prime odd seven le
    have x:(z.1:ZMod q)=0 := by simpa using (ZMod.intCast_eq_intCast_iff ..).mpr rr
    have y:(z.2:ZMod q)=1 := by simpa using (ZMod.intCast_eq_intCast_iff ..).mpr ii
    have adj:(adjacentNorm z s : ZMod q)=(2:ZMod q) := by
      unfold adjacentNorm
      rw [gaussian_residue]
      cases s <;> simp [realResidue,imagResidue,x,y] <;> norm_num
    have non:(2:ZMod q)≠0 :=by
      rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
      exact fun q2=>odd ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp q2)
    exact non (adj.symm.trans ((ZMod.natCast_eq_zero_iff ..).mpr d))

def selfAt (K N q : ℕ) : Finset ℕ :=
  (primeBase K N).filter (fun p=>∃z, gaussianNorm z=p ∧ rayGenerator K z ∧
    q∣adjacentNorm z true ∧ q∣adjacentNorm z false)
def splitPlaces (K R : ℕ) : Finset ℕ :=
  (range (R+1)).filter (fun q=>q.Prime ∧ q%4=1 ∧ K<q)
def farSelf (K N R : ℕ) : Finset ℕ :=
  (primeBase K N).filter (fun p=>∃q>R, q.Prime ∧ q≠2 ∧ p∈selfAt K N q)
def cleanSet (K N : ℕ) : Finset ℕ := (range (N+1)).filter (cleanPrime K)

/-- Every failure on this actual ray can be charged either to two selected
residues at a small split prime, or to an element in the signed lattice tail. -/
theorem ray_sieve (K N R : ℕ) :
    (primeBase K N).card ≤ (cleanSet K N).card +
      (∑ q∈splitPlaces K R,(selfAt K N q).card)+(farSelf K N R).card := by
  classical
  have sub:primeBase K N ⊆ cleanSet K N ∪ (splitPlaces K R).biUnion (selfAt K N) ∪ farSelf K N R := by
    intro p mem
    by_cases good : p∈cleanSet K N
    · exact mem_union_left _ (mem_union_left _ good)
    have bs:=mem_filter.mp mem
    obtain ⟨hp,z,hz,rz⟩:=bs.2
    have fail : ¬(∀q,q.Prime→q≠2→¬(q∣adjacentNorm z true ∧ q∣adjacentNorm z false)) := by
      intro safe
      apply good
      exact mem_filter.mpr ⟨bs.1,hp,z,hz,rz.1,rz.2.1,safe,fun q hh odd low=>finite_guard_free rz hh odd low⟩
    push Not at fail
    obtain ⟨q,qp,odd,plus,minus⟩:=fail
    have item:p∈selfAt K N q:=mem_filter.mpr ⟨mem,z,hz,rz,plus,minus⟩
    by_cases tail:R<q
    · exact mem_union_right _ (mem_filter.mpr ⟨mem,q,tail,qp,odd,item⟩)
    have outside:K<q:=by
      by_contra! short
      exact finite_guard_free rz qp odd short true plus
    let _ : Fact q.Prime:=⟨qp⟩
    have sp: q%4=1 := (self_obstruction odd z plus minus).1
    exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
      ⟨q,mem_filter.mpr ⟨mem_range.mpr (by omega),qp,sp,outside⟩,item⟩))
  exact (card_le_card sub).trans ((card_union_le _ _).trans (Nat.add_le_add_right
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)) _))

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.finite_guard_free
#print axioms Sun28.PeriodWindows.ray_sieve
