import FrobeniusTests
import ClassWeights

namespace Sun28.PrimeClasses
open Sun28.FinitePattern Sun28.PrimeLower Sun28.ContactFactors

/-- One growing one-sign test as an integer expression in the two Frobenius coefficients. -/
def coefficientOrder (n t : ℤ) (s : Bool) : ℤ := n+1+(if s then orient t else -(orient t))

theorem coefficient_order_eq {p : ℕ} (pp : p.Prime) (base : baseRay p) (s : Bool) :
    coefficientOrder p (traceAt p) s=signedOrder p s := by
  let _ : Fact p.Prime := ⟨pp⟩
  rw [coefficientOrder,signedOrder,(oriented_trace (p:=p) ⟨base.1,Or.inl base.2.1⟩).1]

theorem order_periodic {L q : ℕ} (prime : q.Prime) (small : q≤L) {n n' t t' : ℤ}
    (hn : n≡n' [ZMOD modulus L]) (ht : t≡t' [ZMOD modulus L]) (s : Bool) :
    coefficientOrder n t s ≡ coefficientOrder n' t' s [ZMOD q] := by
  have qfactor : q∣modulus L := (Nat.dvd_factorial prime.pos small).trans (dvd_mul_left _ _)
  have dq : (q:ℤ)∣(modulus L:ℤ) := by exact_mod_cast qfactor
  have m8 : (8:ℤ)∣(modulus L:ℤ) := by
    unfold modulus
    push_cast
    exact (by decide : (8:ℤ)∣7168).trans (dvd_mul_right _ _)
  have e8 : t%8=t'%8 := ht.of_dvd m8
  have so : orient t≡orient t' [ZMOD q] := by
    unfold orient
    rw [e8]
    split
    · exact ht.of_dvd dq
    · exact (ht.of_dvd dq).neg
  unfold coefficientOrder
  cases s
  · exact ((hn.of_dvd dq).add (Int.ModEq.refl 1)).add so.neg
  · exact ((hn.of_dvd dq).add (Int.ModEq.refl 1)).add so

def matrixOrder (L q : ℕ) (g : Mat L) (s : Bool) : Prop :=
  ¬(q:ℤ)∣coefficientOrder (g.det.cast : ℤ) (g.trace.cast : ℤ) s

theorem order_of_coefficients {L q p : ℕ} (pp : p.Prime) (base : baseRay p)
    (qp : q.Prime) (small : q≤L) (g : Mat L) (det : g.det=(p:ZMod (modulus L)))
    (tr : g.trace=(traceAt p:ZMod (modulus L))) (s : Bool) :
    (¬(q:ℤ)∣signedOrder p s) ↔ matrixOrder L q g s := by
  have hn : (p:ℤ)≡(g.det.cast : ℤ) [ZMOD modulus L] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp; simpa using det.symm
  have ht : traceAt p≡(g.trace.cast : ℤ) [ZMOD modulus L] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp; simpa using tr.symm
  have h := order_periodic qp small hn ht s
  rw [←coefficient_order_eq pp base s]
  exact not_congr (Int.modEq_zero_iff_dvd.symm.trans
    ((show (_≡0 [ZMOD (q:ℤ)]) ↔ _ from ⟨fun v => h.symm.trans v,fun v => h.trans v⟩).trans
    Int.modEq_zero_iff_dvd))

/-- All growing tests on a concrete row, under the characteristic polynomial identities. -/
theorem row_of_matrices {A : Fin 3→ℚ} {K L : ℕ} {x : ℕ×ℕ}
    (base : ∀ i : ↥(shifts A), commonPrime K K (form A x i).toNat)
    (g : ↥(shifts A)→Mat L)
    (det : ∀ i,(g i).det=((form A x i).toNat:ZMod (modulus L)))
    (tr : ∀ i,(g i).trace=(traceAt (form A x i).toNat:ZMod (modulus L))) :
    extraTest A K L x ↔ ∀ q : ℕ, q.Prime → K<q → q≤L →
      if q%4=3 then ¬((x.1:ZMod q)=1 ∧ (x.2:ZMod q)=0)
      else (∀ i, matrixOrder L q (g i) true) ∨ (∀ i,matrixOrder L q (g i) false) := by
  rw [←crossing_iff base]
  have rows (i : ↥(shifts A)) := (common_prime_iff ..).mp (base i)
  have both (q : ℕ) (qp : q.Prime) (small : q≤L) (s : Bool) :
      (∀ i : ↥(shifts A),¬(q:ℤ)∣signedOrder (form A x i).toNat s) ↔
      ∀ i,matrixOrder L q (g i) s :=
    forall_congr' fun i => order_of_coefficients (rows i).1 (rows i).2.1 qp small (g i) (det i) (tr i) s
  constructor <;> intro H q qp above below <;> have h := H q qp above below
  all_goals
    by_cases inert : q%4=3
    · simpa only [inert,ite_true] using h
    · simpa only [inert,ite_false,both q qp below] using h

end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.coefficient_order_eq
#print axioms Sun28.PrimeClasses.order_periodic
#print axioms Sun28.PrimeClasses.order_of_coefficients
#print axioms Sun28.PrimeClasses.row_of_matrices
