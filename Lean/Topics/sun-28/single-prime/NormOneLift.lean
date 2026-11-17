import NormCircles

namespace Sun28.SinglePrime
open Sun28.MixedSieve

/-- The two coordinates of a Gaussian residue have nonzero norm. -/
def normPair {p : ℕ} (z : F p × F p) : F p := z.1^2+z.2^2

def conjugate {p : ℕ} (z : F p × F p) : F p × F p := (z.1,-z.2)

def times {p : ℕ} (z w : F p × F p) : F p × F p :=
  (z.1*w.1-z.2*w.2,z.2*w.1+z.1*w.2)

theorem norm_times {p : ℕ} (z w : F p × F p) :
    normPair (times z w)=normPair z*normPair w := by dsimp [normPair,times]; ring

/-- Explicit Hilbert 90 on the Gaussian residue algebra, including the split primes. -/
theorem norm_one_lift {p : ℕ} [Fact p.Prime] (odd : p≠2) (z : Circle p 1) :
    ∃ b : F p × F p,normPair b≠0 ∧ times z.val (conjugate b)=b := by
  obtain ⟨⟨x,y⟩,eq⟩:=z
  change x^2+y^2=1 at eq
  have two : (2:F p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun d => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp d)
  by_cases last : x= -1
  · subst x
    have yn : y=0 := (pow_eq_zero_iff (by decide : 2≠0)).mp (by linear_combination eq : y^2=0)
    subst y
    exact ⟨(0,1),by simp [normPair],by simp [times,conjugate]⟩
  · refine ⟨(1+x,y),?_,?_⟩
    · have e : normPair (p:=p) (1+x,y)=2*(1+x) := by dsimp [normPair];linear_combination eq
      rw [e]
      exact mul_ne_zero two (fun h=>last (by linear_combination h))
    · apply Prod.ext <;> dsimp [times,conjugate]
      · linear_combination eq
      · ring

/-- The conjugation quotient of an invertible Gaussian residue is precisely a norm-one point. -/
theorem conjugate_quotient_iff {p : ℕ} [Fact p.Prime] (odd : p≠2) (z : F p × F p) :
    (∃ b,normPair b≠0 ∧ times z (conjugate b)=b) ↔ normPair z=1 := by
  constructor
  · rintro ⟨b,hb,e⟩
    have norm:=congrArg normPair e
    rw [norm_times,show normPair (conjugate b)=normPair b by simp [normPair,conjugate]] at norm
    exact (mul_left_inj' hb).mp (by simpa using norm : normPair z * normPair b=1*normPair b)
  · intro h
    exact norm_one_lift odd ⟨z,h⟩

end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.norm_times
#print axioms Sun28.SinglePrime.norm_one_lift
#print axioms Sun28.SinglePrime.conjugate_quotient_iff
