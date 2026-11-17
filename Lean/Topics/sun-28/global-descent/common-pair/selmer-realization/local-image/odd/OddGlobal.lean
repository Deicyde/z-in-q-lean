import OddUnitRows
import ZInQKernel.RouteK.Selmer.Prop0

namespace Sun28.MarkedOdd
open Sun28.SelmerRealization ZInQ.RouteK ZInQ.RouteK.Selmer

def exponent (p : ℕ) (z : ℤ) : ℕ := if (p:ℤ)∣z then 1 else 0
def primeUnit (p : ℕ) (z : ℤ) : ℤ := if (p:ℤ)∣z then z/p else z

private theorem split_squarefree {p : ℕ} [hp : Fact p.Prime] {z : ℤ} (sz : Squarefree z) :
    exponent p z < 2 ∧ z=(p:ℤ)^(exponent p z)*primeUnit p z ∧ ¬(p:ℤ)∣primeUnit p z := by
  by_cases H : (p:ℤ)∣z
  · simp only [exponent,primeUnit,H,ite_true,pow_one,one_lt_two,true_and]
    have E := Int.ediv_mul_cancel H
    constructor
    · rw [mul_comm];exact E.symm
    · rintro ⟨k,hk⟩
      exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit (sz _ ⟨k,by rw [←E,hk];ring⟩)
  · simp [exponent,primeUnit,H]

/-- The two actual p-adic rows in the normalization dictated by the original
signed squarefree integers. No guessed factorization or residue is required. -/
theorem bad_rows {p : ℕ} [Fact p.Prime] (p2 : p≠2) (p3 : p≠3) {l : ℕ} (pl : p∣l)
    (sl : Squarefree l) {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b)
    (h : Cover (Qp p) l a b) :
    legBit p (primeUnit p a) =
      (exponent p a : ZMod 2)*legBit p ((l:ℤ)/p) + (exponent p b : ZMod 2)*legBit p 3 ∧
    legBit p (primeUnit p b)=(exponent p b : ZMod 2)*legBit p (-((l:ℤ)/p)) := by
  obtain ⟨ax,ae,au⟩ := split_squarefree (p:=p) sa
  obtain ⟨bx,be,bu⟩ := split_squarefree (p:=p) sb
  have L : (p:ℤ)∣(l:ℤ) := by exact_mod_cast pl
  obtain ⟨_,de,du⟩ := split_squarefree (p:=p) (Int.squarefree_natCast.mpr sl)
  simp only [exponent,primeUnit,L,ite_true,pow_one] at de du
  exact bad_rows_of_decomposition p2 p3 pl sl ax bx ae be de au bu du h

theorem local_support_dvd {l : ℕ} (ln : l≠0) {a b : ℤ} (h : (a,b)∈localClasses l) :
    a∣(6*l:ℤ) ∧ b∣(6*l:ℤ) := by
  obtain ⟨sa,sb,_,H⟩ := h
  have ln6 : 6*l≠0 := mul_ne_zero (by decide) ln
  have support (p : ℕ) (pp : p.Prime) (hp : ¬p∣6*l) : ¬(p:ℤ)∣a ∧ ¬(p:ℤ)∣b := by
    let _ : Fact p.Prime := ⟨pp⟩
    have p2 : p≠2 := by rintro rfl; exact hp (dvd_mul_of_dvd_left (by decide) _)
    have p3 : p≠3 := by rintro rfl; exact hp (dvd_mul_of_dvd_left (by decide) _)
    exact good_support p2 p3 (fun d => hp (dvd_mul_of_dvd_right d 6)) sa sb (H p)
  have aa := dvd_of_squarefree_of_odd_primes_dvd ln6 sa
    (fun p pp D => by_contra fun nh => (support p pp nh).1 D)
  have bb := dvd_of_squarefree_of_odd_primes_dvd ln6 sb
    (fun p pp D => by_contra fun nh => (support p pp nh).2 D)
  simpa using And.intro aa bb

end Sun28.MarkedOdd
#print axioms Sun28.MarkedOdd.bad_rows
#print axioms Sun28.MarkedOdd.local_support_dvd
