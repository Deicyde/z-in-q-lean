import DiagonalCover
import ProjectiveContacts
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace ZInQBlueprint.Diagonal210
open Sun28.Ordinary
noncomputable section

/-- Scale factors relating the affine four radicals to Glazer's five primitive forms. -/
def localUnit : Fin 4 → ℚ := ![-7,-3,21,-21/16]

theorem affine_radicand (A B : ℤ) (bn : B≠0) (i : Fin 4) :
    radicand ((A:ℚ)/B) i = localUnit i*((oldForm i.succ A B:ℤ):ℚ)/(B:ℚ) := by
  have bq : (B:ℚ)≠0 := by exact_mod_cast bn
  fin_cases i <;> norm_num [radicand,coefficient,mark,localUnit,oldForm] <;>
    field_simp [bq] ; ring

private theorem small_val {p n : ℕ} (hn : 0<n) (hlt : n<p) : padicValRat p (n:ℚ)=0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (fun d=>(not_le_of_gt hlt) (Nat.le_of_dvd hn d))]
  rfl

private theorem unit_val {p : ℕ} [Fact p.Prime] (hp : 7<p) (i : Fin 4) :
    padicValRat p (localUnit i)=0 := by
  have h3 := small_val (p:=p) (n:=3) (by decide) (by omega)
  have h7 := small_val (p:=p) (n:=7) (by decide) (by omega)
  have h2 := small_val (p:=p) (n:=2) (by decide) (by omega)
  norm_num only [Nat.cast_ofNat] at h2 h3 h7
  have h16 : padicValRat p (16:ℚ)=0 := by
    rw [show (16:ℚ)=2^4 by norm_num,padicValRat.pow,h2,mul_zero]
  have h21 : padicValRat p (21:ℚ)=0 := by
    rw [show (21:ℚ)=3*7 by norm_num,padicValRat.mul (by norm_num) (by norm_num),h3,h7,add_zero]
  fin_cases i
  · change padicValRat p (-(7:ℚ))=0
    simpa only [padicValRat.neg] using h7
  · change padicValRat p (-(3:ℚ))=0
    simpa only [padicValRat.neg] using h3
  · exact h21
  · change padicValRat p ((-(21:ℚ))/16)=0
    rw [padicValRat.div (by norm_num) (by norm_num),padicValRat.neg,h21,h16,sub_zero]

theorem valuation_of_radicand {p : ℕ} [Fact p.Prime] (large : 7<p) {A B : ℤ}
    (hn : ∀ i, oldForm i A B≠0) (i : Fin 4) :
    padicValRat p (radicand ((A:ℚ)/B) i)=
      (padicValInt p (oldForm i.succ A B):ℤ) - (padicValInt p B:ℤ) := by
  have bn : B≠0 := by simpa [oldForm] using hn 0
  have bq : (B:ℚ)≠0 := by exact_mod_cast bn
  have fq : (oldForm i.succ A B:ℚ)≠0 := by exact_mod_cast hn i.succ
  have un : localUnit i ≠ 0 := by fin_cases i <;> norm_num [localUnit]
  rw [affine_radicand A B bn,padicValRat.div (mul_ne_zero un fq) bq,padicValRat.mul un fq,
    unit_val large,padicValRat.of_int,padicValRat.of_int,zero_add]

private theorem primitive_zero (p : ℕ) (hp : p.Prime) {A B : ℤ} (cop : Int.gcd A B=1) :
    padicValInt p A=0 ∨ padicValInt p B=0 := by
  have cop' : Nat.Coprime A.natAbs B.natAbs := by simpa [Int.gcd,Nat.Coprime] using cop
  by_cases a : p∣A.natAbs
  · have b : ¬p∣B.natAbs := fun d=>Nat.not_coprime_of_dvd_of_dvd hp.one_lt a d cop'
    exact Or.inr (padicValNat.eq_zero_of_not_dvd b)
  · exact Or.inl (padicValNat.eq_zero_of_not_dvd a)

/-- Off the marks, Glazer's old contact primes are exactly those where one of the
four explicit defining radicals has odd valuation. The denominator accounts for infinity. -/
theorem odd_radicand_iff_contact {p : ℕ} [Fact p.Prime] (large : 7<p) {A B : ℤ}
    (cop : Int.gcd A B=1) (hn : ∀ i,oldForm i A B≠0) (S : Finset ℕ) (out : p∉S) :
    (∃ i,Odd (padicValRat p (radicand ((A:ℚ)/B) i))) ↔ p∈oldContactPrimes S A B := by
  rw [mem_oldContactPrimes]
  have prime : p.Prime := Fact.out
  have zero : padicValInt p (oldForm 0 A B)=padicValInt p B := by simp [oldForm]
  constructor
  · rintro ⟨i,hi⟩
    rw [valuation_of_radicand large hn] at hi
    refine ⟨prime,out,?_⟩
    rw [Int.odd_iff] at hi
    by_cases hb : Odd (padicValInt p B)
    · refine ⟨0,?_,zero ▸ hb⟩
      rw [zero]
      rw [Nat.odd_iff] at hb
      omega
    · rw [Nat.not_odd_iff] at hb
      exact ⟨i.succ,by omega,Nat.odd_iff.mpr (by omega)⟩
  · rintro ⟨_,_,j,pos,odd⟩
    by_cases hb : Odd (padicValInt p B)
    · have parity := Nat.odd_iff.mp hb
      have bp : 0<padicValInt p B := by omega
      have av : padicValInt p A=0 := (primitive_zero p prime cop).resolve_right (by omega)
      refine ⟨0,?_⟩
      rw [valuation_of_radicand large hn]
      change Odd ((padicValInt p A:ℤ)-(padicValInt p B:ℤ))
      rw [Int.odd_iff,av]
      omega
    · refine Fin.cases (motive:=fun j=>0<padicValInt p (oldForm j A B)→Odd (padicValInt p (oldForm j A B))→
          ∃ i,Odd (padicValRat p (radicand ((A:ℚ)/B) i))) ?_ ?_ j pos odd
      · rw [zero]
        exact fun _ h=>(hb h).elim
      · intro i _ d
        refine ⟨i,?_⟩
        rw [valuation_of_radicand large hn,Int.odd_iff]
        rw [Nat.odd_iff] at d
        rw [Nat.not_odd_iff] at hb
        omega

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.valuation_of_radicand
#print axioms ZInQBlueprint.Diagonal210.odd_radicand_iff_contact
