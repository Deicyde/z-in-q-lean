import OriginalRows
import CrossRatioForms

namespace ZInQBlueprint.FiveCovers
open Finset Sun28.Ordinary Sun28.HeightFibres Sun28.FiveMarkTriples ZInQ.RouteK
noncomputable section

def rowPrimes (i : Fin 5) (A B : ℤ) : Finset ℕ := (formPrimes i A B).filter
  fun p => Odd ((oldForm i A B).natAbs.factorization p)

def hitRows (A B : ℤ) (p : ℕ) : Finset (Fin 5) := univ.filter fun i => p∈rowPrimes i A B

def multiplicity (p : ℕ) : ℕ := if p=2 then 2 else if p=3 ∨ p=5 ∨ p=7 then 3 else 1

theorem radical_row (i : Fin 5) {A B : ℤ} (off : oldForm i A B≠0) :
    (kernel i A B).natAbs = Sun28.FiveMarkUnits.primeProduct (rowPrimes i A B) := by
  change (sqfInt (oldForm i A B)).natAbs=_
  rw [sqfInt,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero off,Int.natAbs_natCast,one_mul]
  rfl

private def residueRows (p : ℕ) [NeZero p] (a b : ZMod p) : Finset (Fin 5) :=
  univ.filter fun i => (coeffA i:ZMod p)*a+(coeffB i:ZMod p)*b=0

private theorem residue_bound {p k : ℕ} [NeZero p] (pr : p.Prime)
    (table : ∀ a b : ZMod p, a≠0 ∨ b≠0 → (residueRows p a b).card≤k)
    {A B : ℤ} (cop : Int.gcd A B=1) : (hitRows A B p).card≤k := by
  have nz : (A:ZMod p)≠0 ∨ (B:ZMod p)≠0 := by
    by_contra! z
    have g := Int.dvd_coe_gcd ((ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp z.1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd B p).mp z.2)
    rw [cop] at g
    exact pr.not_dvd_one (Int.natCast_dvd_natCast.mp g)
  apply (card_le_card (t:=residueRows p A B) ?_).trans (table _ _ nz)
  intro i hi
  have r := (mem_filter.mp (mem_filter.mp hi).2).1
  have d : (p:ℤ)∣oldForm i A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors r)
  have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr d
  rw [form_coeff] at zero
  exact mem_filter.mpr ⟨mem_univ _,by simpa only [Int.cast_add,Int.cast_mul] using zero⟩

private theorem common_minor {p : ℕ} {A B : ℤ} {i j : Fin 5} (pr : p.Prime) (cop : Int.gcd A B=1)
    (di : p∈formPrimes i A B) (dj : p∈formPrimes j A B) : (p:ℤ)∣det i j := by
  by_contra nd
  have pi : Prime (p:ℤ) := by simpa [Int.prime_iff_natAbs_prime] using pr
  have a : (p:ℤ)∣oldForm i A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors di)
  have b : (p:ℤ)∣oldForm j A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors dj)
  have dA : (p:ℤ)∣det i j*A := by
    have m := dvd_sub (dvd_mul_of_dvd_right a (coeffB j)) (dvd_mul_of_dvd_right b (coeffB i))
    convert m using 1
    simp only [det,form_coeff];ring
  have dB : (p:ℤ)∣det i j*B := by
    have m := dvd_sub (dvd_mul_of_dvd_right b (coeffA i)) (dvd_mul_of_dvd_right a (coeffA j))
    convert m using 1
    simp only [det,form_coeff];ring
  have g := Int.dvd_coe_gcd ((pi.dvd_mul.mp dA).resolve_left nd) ((pi.dvd_mul.mp dB).resolve_left nd)
  rw [cop] at g
  exact pr.not_dvd_one (Int.natCast_dvd_natCast.mp g)

/-- Number of squarefree row coefficients in which one prime can occur. -/
theorem prime_multiplicity {A B : ℤ} (cop : Int.gcd A B=1) {p : ℕ} (pr : p.Prime) :
    (hitRows A B p).card ≤ multiplicity p := by
  by_cases p2 : p=2
  · subst p; exact residue_bound (by decide : Nat.Prime 2) (k:=2) (by decide) cop
  by_cases p3 : p=3
  · subst p; exact residue_bound (by decide : Nat.Prime 3) (k:=3) (by decide) cop
  by_cases p5 : p=5
  · subst p; exact residue_bound (by decide : Nat.Prime 5) (k:=3) (by decide) cop
  by_cases p7 : p=7
  · subst p; exact residue_bound (by decide : Nat.Prime 7) (k:=3) (by decide) cop
  simp only [multiplicity,p2,p3,p5,p7,or_self,ite_false]
  apply card_le_one.mpr
  intro i hi j hj
  by_contra ne
  have h := common_minor pr cop (mem_filter.mp (mem_filter.mp hi).2).1 (mem_filter.mp (mem_filter.mp hj).2).1
  have catalogue : ∀ i j : Fin 5, i≠j → (det i j).natAbs∣(2*3*5*7)^8 := by decide
  have dv : p∣(2*3*5*7)^8 := (show p∣(det i j).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (catalogue i j ne)
  have f : p ∣ (2*3*5*7) := pr.dvd_of_dvd_pow dv
  have np {q : ℕ} (hq : q.Prime) (ne : p≠q) : ¬p∣q := fun h=> ne ((Nat.prime_dvd_prime_iff_eq pr hq).mp h)
  simp only [pr.dvd_mul,np (by decide : Nat.Prime 2) p2,np (by decide : Nat.Prime 3) p3,
    np (by decide : Nat.Prime 5) p5,np (by decide : Nat.Prime 7) p7,or_self] at f

end
end ZInQBlueprint.FiveCovers
#print axioms ZInQBlueprint.FiveCovers.radical_row
#print axioms ZInQBlueprint.FiveCovers.prime_multiplicity
