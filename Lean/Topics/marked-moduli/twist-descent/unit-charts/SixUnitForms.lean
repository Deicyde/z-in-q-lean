import RationalLocalization

/-! A rational unit equation in every triple of the six twist forms. -/
namespace ZInQBlueprint.SixUnitCharts
open Sun28.Ordinary Sun28.FiveMarkUnits

def coeffA (i : Fin 6) : ℤ := ![0,1,1,1,1,1] i
def coeffB (i : Fin 6) : ℤ := ![1,0,-1,1,-3,3] i
def det (i j : Fin 6) : ℤ := coeffA i*coeffB j-coeffA j*coeffB i

def row (i : Fin 6) (a b : ℤ) : ℤ := coeffA i*a+coeffB i*b

def fixedPrimes : Finset ℕ := {2,3}

theorem form_coeff (i : Fin 6) (a b : ℤ) : row i a b=coeffA i*a+coeffB i*b := rfl

theorem det_ne {i j : Fin 6} (diff : i≠j) : det i j≠0 := by
  have all : ∀ i j : Fin 6, i≠j → det i j≠0 := by decide
  exact all i j diff

theorem determinant_support (i j : Fin 6) : (det i j).natAbs.primeFactors ⊆ fixedPrimes := by
  intro p hp
  obtain ⟨prime,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
  have catalogue : ∀ i j : Fin 6, det i j≠0 → (det i j).natAbs ∣ 12 := by decide
  have d : p∣2^2*3 := dvd.trans (catalogue i j (Int.natAbs_ne_zero.mp nz))
  rcases prime.dvd_mul.mp d with two|three
  · have h := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp (prime.dvd_of_dvd_pow two)
    simp [fixedPrimes,h]
  · have h := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_three).mp three
    simp [fixedPrimes,h]

theorem minor_identity (i j k : Fin 6) (A B : ℤ) :
    det k j*row i A B+det i k*row j A B=det i j*row k A B := by
  simp only [det,form_coeff]
  ring

def formPrimes (i : Fin 6) (A B : ℤ) := (row i A B).natAbs.primeFactors

def triplePrimes (i j k : Fin 6) (A B : ℤ) : Finset ℕ :=
  formPrimes i A B ∪ formPrimes j A B ∪ formPrimes k A B

def crossRatio (i j k : Fin 6) (A B : ℤ) : ℚ :=
  ((det k j*row i A B:ℤ):ℚ)/((det i j*row k A B:ℤ):ℚ)

theorem localised_pair {i j k : Fin 6} (ij : i≠j) (ik : i≠k) (jk : j≠k) (A B : ℤ)
    (off : ∀ n,row n A B≠0) :
    let S := fixedPrimes ∪ triplePrimes i j k A B
    let x := crossRatio i j k A B
    RationalSUnit S x ∧ RationalSUnit S (1-x) := by
  let S:=fixedPrimes ∪ triplePrimes i j k A B
  have part₁ : formPrimes i A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ m))
  have part₂ : formPrimes j A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ m))
  have part₃ : formPrimes k A B⊆S := fun _ m => Finset.mem_union_right _ (Finset.mem_union_right _ m)
  have product (u v n : Fin 6) (uv : u≠v) (subset : formPrimes n A B⊆S) :
      (det u v*row n A B).natAbs.primeFactors⊆S := by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne uv)) (Int.natAbs_ne_zero.mpr (off n))]
    exact Finset.union_subset (fun _ h => Finset.mem_union_left _ (determinant_support u v h)) subset
  have dn := mul_ne_zero (det_ne ij) (off k)
  have common := product i j k ij part₃
  have u := ratio_unit (mul_ne_zero (det_ne jk.symm) (off i)) dn (product k j i jk.symm part₁) common
  have v := ratio_unit (mul_ne_zero (det_ne ik) (off j)) dn (product i k j ik part₂) common
  let y := ((det i k*row j A B:ℤ):ℚ)/((det i j*row k A B:ℤ):ℚ)
  have eq : crossRatio i j k A B+y=1 := by
    unfold crossRatio y
    rw [←add_div,←Int.cast_add,minor_identity,div_self (by exact_mod_cast dn)]
  exact ⟨u,(show 1-crossRatio i j k A B=y by linarith).symm ▸ v⟩

theorem support_prime {i j k : Fin 6} {A B : ℤ} {p : ℕ} (h : p∈triplePrimes i j k A B) : p.Prime := by
  rcases Finset.mem_union.mp h with a|b
  · rcases Finset.mem_union.mp a with x|x
    · exact Nat.prime_of_mem_primeFactors x
    · exact Nat.prime_of_mem_primeFactors x
  · exact Nat.prime_of_mem_primeFactors b

/-- Outside the cutoff, primitivity prevents two distinct forms vanishing mod p. -/
theorem unique_form {i j : Fin 6} {A B : ℤ} (primitive : Int.gcd A B=1)
    {p : ℕ} (away : p∉fixedPrimes) (hi : p∈formPrimes i A B) (hj : p∈formPrimes j A B) : i=j := by
  by_contra distinct
  have prime := Nat.prime_of_mem_primeFactors hi
  have P : Prime (p:ℤ) := by simpa [Int.prime_iff_natAbs_prime] using prime
  have a : (p:ℤ) ∣ row i A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hi)
  have b : (p:ℤ) ∣ row j A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hj)
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

end ZInQBlueprint.SixUnitCharts
#print axioms ZInQBlueprint.SixUnitCharts.form_coeff
#print axioms ZInQBlueprint.SixUnitCharts.determinant_support
#print axioms ZInQBlueprint.SixUnitCharts.minor_identity
#print axioms ZInQBlueprint.SixUnitCharts.localised_pair
#print axioms ZInQBlueprint.SixUnitCharts.unique_form
