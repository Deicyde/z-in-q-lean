import GaussianHeader
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic

def orderLcm {ι : Type*} [Fintype ι] (π : ι → Gaussian) (sign : Bool) : ℕ :=
  Finset.univ.lcm fun i => adjacentNorm (π i) sign

theorem prime_dvd_lcm_iff {ι : Type*} (s : Finset ι) (f : ι→ℕ) {p : ℕ} (hp : p.Prime) :
    p∣s.lcm f ↔ ∃ i∈s,p∣f i := by
  constructor
  · intro d
    have bound : s.lcm f∣∏ i∈s,f i := Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem f hi)
    exact (Nat.prime_iff.mp hp |>.dvd_finsetProd_iff f).mp (d.trans bound)
  · rintro ⟨i,hi,d⟩
    exact d.trans (Finset.dvd_lcm hi)

private theorem lcm_factorization_le {ι : Type*} (s : Finset ι) (f : ι→ℕ) (p e : ℕ)
    (nz : ∀ i∈s,f i≠0) (bound : ∀ i∈s,(f i).factorization p≤e) :
    (s.lcm f).factorization p≤e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s fresh ih =>
    have nz' : ∀ j∈s,f j≠0 := fun j hj=>nz j (Finset.mem_insert_of_mem hj)
    have le' := ih nz' (fun j hj=>bound j (Finset.mem_insert_of_mem hj))
    rw [Finset.lcm_insert]
    change ((f i).lcm (s.lcm f)).factorization p≤e
    rw [Nat.factorization_lcm (nz i (Finset.mem_insert_self ..)) (Finset.lcm_ne_zero_iff.mpr nz')]
    exact max_le (bound i (Finset.mem_insert_self ..)) le'

theorem constant_order_lcm {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι→ℕ)
    {p e : ℕ} (hp : p.Prime) (nz : ∀ i∈s,f i≠0) (v : ∀ i∈s,padicValNat p (f i)=e) :
    padicValNat p (s.lcm f)=e := by
  have each (i) (hi : i∈s) : (f i).factorization p=e := (Nat.factorization_def _ hp).trans (v i hi)
  rw [← Nat.factorization_def _ hp]
  obtain ⟨i,hi⟩:=hs
  apply le_antisymm (lcm_factorization_le s f p e nz (fun j hj=>(each j hj).le))
  rw [← each i hi]
  exact ((Nat.factorization_le_iff_dvd (nz i hi) (Finset.lcm_ne_zero_iff.mpr nz)).mpr
    (Finset.dvd_lcm hi)) p

theorem pairwise_gcd_lcms {ι : Type*} (s : Finset ι) (f g : ι→ℕ)
    (f0 : ∀ i∈s,f i≠0) (g0 : ∀ i∈s,g i≠0)
    (f2 : padicValNat 2 (s.lcm f)=2) (g2 : padicValNat 2 (s.lcm g)=6)
    (cross : ∀ i∈s,∀ j∈s,(f i).gcd (g j)=4) : (s.lcm f).gcd (s.lcm g)=4 := by
  have fnz:=Finset.lcm_ne_zero_iff.mpr f0
  have gnz:=Finset.lcm_ne_zero_iff.mpr g0
  apply Nat.eq_of_factorization_eq (by simp [Nat.gcd_eq_zero_iff,fnz]) (by decide)
  intro p
  by_cases two : p=2
  · subst p
    rw [Nat.factorization_gcd fnz gnz]
    change min ((s.lcm f).factorization 2) ((s.lcm g).factorization 2) = Nat.factorization 4 2
    rw [Nat.factorization_def _ Nat.prime_two,Nat.factorization_def _ Nat.prime_two,f2,g2]
    rw [Nat.factorization_def _ Nat.prime_two]
    exact (padicValNat.prime_pow (p:=2) 2).symm
  by_cases prime : p.Prime
  · have off : ¬p∣4 := by
      have two2 : 4=2*2 := rfl
      rw [two2,prime.dvd_mul]
      simpa [Nat.prime_dvd_prime_iff_eq prime Nat.prime_two] using (show ¬(p=2 ∨ p=2) by simp [two])
    have other : ¬p∣(s.lcm f).gcd (s.lcm g) := by
      intro d
      obtain ⟨i,hi,fi⟩ := (prime_dvd_lcm_iff s f prime).mp (d.trans (Nat.gcd_dvd_left ..))
      obtain ⟨j,hj,gj⟩ := (prime_dvd_lcm_iff s g prime).mp (d.trans (Nat.gcd_dvd_right ..))
      exact off ((cross i hi j hj) ▸ Nat.dvd_gcd fi gj)
    rw [Nat.factorization_eq_zero_of_not_dvd other,Nat.factorization_eq_zero_of_not_dvd off]
  · rw [Nat.factorization_eq_zero_of_not_prime _ prime,Nat.factorization_eq_zero_of_not_prime _ prime]

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.prime_dvd_lcm_iff
#print axioms Sun28.GaussianSelection.constant_order_lcm
#print axioms Sun28.GaussianSelection.pairwise_gcd_lcms
