import CoefficientClass
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Sun28.PrimeClasses
open Matrix Sun28.FinitePattern

/-- The one field used at cutoff L can be taken to be ℚ(E[modulus L]). -/
def modulus (L : ℕ) : ℕ := 7168*L.factorial

theorem coefficient_periodic {L : ℕ} {n n' t t' : ℤ}
    (hn : n≡n' [ZMOD modulus L]) (ht : t≡t' [ZMOD modulus L]) :
    coefficientClass L n t ↔ coefficientClass L n' t' := by
  have large (m : ℤ) (h : m∣7168) : m ∣ (modulus L:ℤ) := by
    unfold modulus
    push_cast
    exact h.trans (dvd_mul_right 7168 _)
  have orientCong (m : ℤ) (h : m∣7168) : orient t ≡ orient t' [ZMOD m] := by
    have e : t%8=t'%8 := ht.of_dvd (large 8 (by decide))
    unfold orient
    rw [e]
    split
    · exact ht.of_dvd (large m h)
    · exact (ht.of_dvd (large m h)).neg
  have check {a b k : ℤ} (h : a≡b [ZMOD k]) (c : ℤ) : (a≡c [ZMOD k]) ↔ (b≡c [ZMOD k]) :=
    ⟨fun v => h.symm.trans v,fun v => h.trans v⟩
  have base : coefficientBase n t ↔ coefficientBase n' t' := by
    unfold coefficientBase
    have n1024 := (hn.of_dvd (large 1024 (by decide))).mul_left 4
    have t1024 := (ht.of_dvd (large 1024 (by decide))).pow 2
    refine and_congr (check (hn.of_dvd (large 8 (by decide))) _) (and_congr
      (check (hn.of_dvd (large 7 (by decide))) _) (and_congr
      (check (orientCong 32 (by decide)) _) (and_congr (check (orientCong 14 (by decide)) _) ?_)))
    exact ⟨fun h => n1024.symm.trans (h.trans t1024),fun h => n1024.trans (h.trans t1024.symm)⟩
  have kill (q : ℕ) (qp : q.Prime) (small : q≤L) :
      (q:ℤ)∣(n+1)^2-t^2 ↔ (q:ℤ)∣(n'+1)^2-t'^2 := by
    have qfactor : q∣modulus L := (Nat.dvd_factorial qp.pos small).trans (dvd_mul_left _ _)
    have dq : (q:ℤ)∣(modulus L:ℤ) := by exact_mod_cast qfactor
    have e := ((hn.of_dvd dq).add (Int.ModEq.refl 1)).pow 2
    exact (Int.modEq_zero_iff_dvd.symm.trans (check (e.sub ((ht.of_dvd dq).pow 2)) _)).trans
      Int.modEq_zero_iff_dvd
  unfold coefficientClass
  apply and_congr base
  constructor <;> intro h q qp two seven bound
  · exact fun v => h q qp two seven bound ((kill q qp bound).mpr v)
  · exact fun v => h q qp two seven bound ((kill q qp bound).mp v)

abbrev Mat (L : ℕ) := Matrix (Fin 2) (Fin 2) (ZMod (modulus L))

/-- A matrix class function, computed from determinant and trace by lifting from Z/M. -/
def matrixClass (L : ℕ) (g : Mat L) : Prop :=
  coefficientClass L (g.det.cast : ℤ) (g.trace.cast : ℤ)

theorem matrix_class_conjugation (L : ℕ) (g u v : Mat L) (inverse : v*u=1) :
    matrixClass L (u*g*v) ↔ matrixClass L g := by
  have dd := congrArg Matrix.det inverse
  rw [det_mul,det_one] at dd
  have dt : (u*g*v).det=g.det := by rw [det_mul,det_mul]; calc
    u.det*g.det*v.det = (v.det*u.det)*g.det := by ring
    _ = g.det := by rw [dd,one_mul]
  have tr : (u*g*v).trace=g.trace := by
    rw [trace_mul_comm,←Matrix.mul_assoc,inverse,Matrix.one_mul]
  rw [matrixClass,matrixClass,dt,tr]

theorem class_of_coefficients (L p : ℕ) (g : Mat L) (det : g.det=(p:ZMod (modulus L)))
    (tr : g.trace=(traceAt p:ZMod (modulus L))) :
    commonPrime L L p ↔ p.Prime ∧ matrixClass L g := by
  rw [common_both_iff]
  refine and_congr_right fun _ => ?_
  unfold matrixClass
  apply coefficient_periodic
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa using det.symm
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa using tr.symm

end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.coefficient_periodic
#print axioms Sun28.PrimeClasses.matrix_class_conjugation
#print axioms Sun28.PrimeClasses.class_of_coefficients
