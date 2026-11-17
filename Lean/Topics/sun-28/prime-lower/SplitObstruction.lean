import CommonPrimes

namespace Sun28.PrimeLower

open Finset Sun28.MixedSieve Sun28.FinitePattern
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Split primes retain a bad representative of *every* rational norm, for each sign. -/
theorem split_bad_all (split : p%4=1) (t : ZMod p) (e : Bool) :
    (bad p t e).Nonempty := by
  have two : (2:ZMod p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun h => (show p≠2 by omega) ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
  obtain ⟨j,hj⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega : p%4≠3)
  have js : j^2 = -1 := by simpa [pow_two] using hj.symm
  let a : ZMod p := (t+1)/2
  let b : ZMod p := j*(t-1)/2
  have n : a^2+b^2=t := by
    dsimp [a,b]; field_simp; linear_combination (t-1)^2*js
  have h : (a-1)^2+b^2=0 := by
    dsimp [a,b]; field_simp; linear_combination (t-1)^2*js
  cases e
  · refine ⟨⟨(a,b),n⟩,Finset.mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    simpa [sub_eq_add_neg] using h
  · refine ⟨⟨(-a,b),by simpa using n⟩,Finset.mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    change (-a+1)^2+b^2=0
    linear_combination h

/-- The projective trace parameter is unnecessary here. Away from t=1 there
are two forbidden lifts per sign, and t=1 has just one. -/
theorem split_bad_card (split : p%4=1) (t : ZMod p) (e : Bool) :
    (bad p t e).card = if t=1 then 1 else 2 := by
  have hp : p≠2 := by omega
  have two : (2:ZMod p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun h => hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
  obtain ⟨z,hz⟩ := split_bad_all split t e
  let refl (z : Circle p t) : Circle p t := ⟨(z.val.1,-z.val.2),by simpa using z.property⟩
  have hr : refl z ∈ bad p t e := Finset.mem_filter.mpr ⟨mem_univ _,by
    simpa [refl] using (Finset.mem_filter.mp hz).2⟩
  have fixed (v : Circle p t) (hv : v∈bad p t e) :
      v.val.1 = Sun28.NormSieve.signedCoordinate t e :=
    Sun28.NormSieve.fixed_real hp _ _ _ v.property e (Finset.mem_filter.mp hv).2
  by_cases ht : t=1
  · subst t
    have ys (v : Circle p 1) (hv : v∈bad p 1 e) : v.val.2=0 := by
      have fx := fixed v hv
      have rel:=v.property
      have normx : v.val.1^2=1 := by
        rw [fx]
        cases e <;> simp only [Sun28.NormSieve.signedCoordinate,Bool.false_eq_true,ite_false,ite_true] <;> field_simp <;> ring
      rw [normx] at rel
      have yy : v.val.2^2=0 := by linear_combination rel
      simpa using yy
    have seteq : bad p 1 e={z} := by
      ext v
      constructor
      · intro hv
        apply mem_singleton.mpr
        apply Subtype.ext
        exact Prod.ext ((fixed v hv).trans (fixed z hz).symm) ((ys v hv).trans (ys z hz).symm)
      · rintro hv
        exact (mem_singleton.mp hv) ▸ hz
    simp [seteq]
  · have yn : z.val.2 ≠ 0 := by
      intro yz
      have c := (Finset.mem_filter.mp hz).2
      rw [yz] at c
      have x : z.val.1+(if e then 1 else -1)=0 := by simpa using c
      have n:=z.property
      rw [yz] at n
      apply ht
      cases e
      · change z.val.1 + -1=0 at x
        have eq : z.val.1=1 := by linear_combination x
        simpa [eq] using n.symm
      · change z.val.1+1=0 at x
        have eq : z.val.1= -1 := by linear_combination x
        simpa [eq] using n.symm
    have diff : z≠refl z := by
      intro he
      have c := congrArg (fun v : Circle p t => v.val.2) he
      change z.val.2 = -z.val.2 at c
      exact yn ((mul_eq_zero.mp (show (2:ZMod p)*z.val.2=0 by linear_combination c)).resolve_left two)
    have lb : 2 ≤ (bad p t e).card := by
      apply (show ({z,refl z} : Finset _).card=2 by simp [diff]).ge.trans
      apply card_le_card
      intro v hv
      rw [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hz
      · exact hr
    simpa [ht] using le_antisymm (bad_card hp _ _) lb

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.split_bad_all
#print axioms Sun28.PrimeLower.split_bad_card
