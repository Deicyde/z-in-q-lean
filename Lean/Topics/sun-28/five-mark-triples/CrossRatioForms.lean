import RationalLocalization

/-! A rational unit equation in every triple of the five original forms. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits

def coeffA (i : Fin 5) : ℤ := ![0,1,1,1,32] i
def coeffB (i : Fin 5) : ℤ := ![1,0,-1,-2401,343] i
def det (i j : Fin 5) : ℤ := coeffA i*coeffB j-coeffA j*coeffB i

theorem form_coeff (i : Fin 5) (A B : ℤ) : oldForm i A B=coeffA i*A+coeffB i*B := by
  fin_cases i <;> simp [oldForm,coeffA,coeffB] <;> ring

theorem det_ne {i j : Fin 5} (diff : i≠j) : det i j≠0 := by
  have all : ∀ i j : Fin 5, i≠j → det i j≠0 := by decide
  exact all i j diff

theorem determinant_support (i j : Fin 5) : (det i j).natAbs.primeFactors ⊆ oldCutoff := by
  intro p hp
  obtain ⟨prime,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
  have catalogue : ∀ i j : Fin 5, det i j≠0 → (det i j).natAbs∣(2*3*5*7)^8 := by decide
  have factor := prime.dvd_of_dvd_pow (dvd.trans (catalogue i j (Int.natAbs_ne_zero.mp nz)))
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have le := Nat.le_of_dvd (by decide : 0<2*3*5*7) factor;omega),prime⟩

theorem minor_identity (i j k : Fin 5) (A B : ℤ) :
    det k j*oldForm i A B+det i k*oldForm j A B=det i j*oldForm k A B := by
  simp only [det,form_coeff]
  ring

def formPrimes (i : Fin 5) (A B : ℤ) := (oldForm i A B).natAbs.primeFactors

def triplePrimes (i j k : Fin 5) (A B : ℤ) : Finset ℕ :=
  formPrimes i A B ∪ formPrimes j A B ∪ formPrimes k A B

def crossRatio (i j k : Fin 5) (A B : ℤ) : ℚ :=
  ((det k j*oldForm i A B:ℤ):ℚ)/((det i j*oldForm k A B:ℤ):ℚ)

theorem localised_pair {i j k : Fin 5} (ij : i≠j) (ik : i≠k) (jk : j≠k) (A B : ℤ)
    (off : ∀ n,oldForm n A B≠0) :
    let S := oldCutoff ∪ triplePrimes i j k A B
    let x := crossRatio i j k A B
    RationalSUnit S x ∧ RationalSUnit S (1-x) := by
  let S:=oldCutoff ∪ triplePrimes i j k A B
  have part₁ : formPrimes i A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ m))
  have part₂ : formPrimes j A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ m))
  have part₃ : formPrimes k A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_right _ m)
  have product (u v n : Fin 5) (uv : u≠v) (subset : formPrimes n A B⊆S) :
      (det u v*oldForm n A B).natAbs.primeFactors⊆S := by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne uv)) (Int.natAbs_ne_zero.mpr (off n))]
    exact Finset.union_subset (fun _ h => Finset.mem_union_left _ (determinant_support u v h)) subset
  have dn := mul_ne_zero (det_ne ij) (off k)
  have common := product i j k ij part₃
  have u := ratio_unit (mul_ne_zero (det_ne jk.symm) (off i)) dn (product k j i jk.symm part₁) common
  have v := ratio_unit (mul_ne_zero (det_ne ik) (off j)) dn (product i k j ik part₂) common
  let y := ((det i k*oldForm j A B:ℤ):ℚ)/((det i j*oldForm k A B:ℤ):ℚ)
  have eq : crossRatio i j k A B+y=1 := by
    unfold crossRatio y
    rw [←add_div,←Int.cast_add,minor_identity,div_self (by exact_mod_cast dn)]
  exact ⟨u,(show 1-crossRatio i j k A B=y by linarith).symm ▸ v⟩

theorem support_prime {i j k : Fin 5} {A B : ℤ} {p : ℕ} (h : p∈triplePrimes i j k A B) : p.Prime := by
  rcases Finset.mem_union.mp h with a|b
  · rcases Finset.mem_union.mp a with x|x
    · exact Nat.prime_of_mem_primeFactors x
    · exact Nat.prime_of_mem_primeFactors x
  · exact Nat.prime_of_mem_primeFactors b

/-- Outside the cutoff, primitivity prevents two distinct forms vanishing mod p. -/
theorem unique_form {i j : Fin 5} {A B : ℤ} (primitive : Int.gcd A B=1)
    {p : ℕ} (away : p∉oldCutoff) (hi : p∈formPrimes i A B) (hj : p∈formPrimes j A B) : i=j := by
  by_contra distinct
  have prime := Nat.prime_of_mem_primeFactors hi
  have P : Prime (p:ℤ) := by simpa [Int.prime_iff_natAbs_prime] using prime
  have a : (p:ℤ) ∣ oldForm i A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hi)
  have b : (p:ℤ) ∣ oldForm j A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hj)
  have nd : ¬(p:ℤ)∣det i j := by
    intro d
    apply away (determinant_support i j ?_)
    exact Nat.mem_primeFactors.mpr ⟨prime,by simpa using Int.natAbs_dvd_natAbs.mpr d,Int.natAbs_ne_zero.mpr (det_ne distinct)⟩
  have da : (p:ℤ)∣det i j*A := by
    have m := dvd_sub (dvd_mul_of_dvd_right a (coeffB j)) (dvd_mul_of_dvd_right b (coeffB i))
    convert m using 1
    simp only [det,form_coeff]
    ring
  have db : (p:ℤ)∣det i j*B := by
    have m := dvd_sub (dvd_mul_of_dvd_right b (coeffA i)) (dvd_mul_of_dvd_right a (coeffA j))
    convert m using 1
    simp only [det,form_coeff]
    ring
  have g := Int.dvd_coe_gcd ((P.dvd_mul.mp da).resolve_left nd) ((P.dvd_mul.mp db).resolve_left nd)
  rw [primitive] at g
  exact prime.not_dvd_one (Int.natCast_dvd_natCast.mp g)

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.form_coeff
#print axioms Sun28.FiveMarkTriples.determinant_support
#print axioms Sun28.FiveMarkTriples.minor_identity
#print axioms Sun28.FiveMarkTriples.localised_pair
#print axioms Sun28.FiveMarkTriples.unique_form
