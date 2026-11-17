import SixComplement

/-! Only primes away from the twisting integer enter the remaining product. -/
namespace ZInQBlueprint.SixUnitCharts
open Sun28.FiveMarkUnits ZInQ ZInQBlueprint.OddSupport ZInQBlueprint.TwistDescent
noncomputable section

def extraPrimes (d : ℤ) (x : ℚ) : Finset ℕ :=
  rowSupport Finset.univ x.num x.den \ (30*d.natAbs).primeFactors

def extraProduct (d : ℤ) (x : ℚ) : ℕ := primeProduct (extraPrimes d x)

theorem support_split {d : ℤ} (hd : d≠0) (x : ℚ) :
    primeProduct (rowSupport Finset.univ x.num x.den)≤30*d.natAbs*extraProduct d x := by
  let S := rowSupport Finset.univ x.num x.den
  let T := (30*d.natAbs).primeFactors
  have inc : S ⊆ T ∪ (S\T) := by
    intro p hp
    by_cases t : p∈T
    · exact Finset.mem_union_left _ t
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,t⟩)
  have primeS (p : ℕ) (mem : p∈S) : p.Prime := by
    rcases Finset.mem_union.mp mem with f|r
    · simp only [fixedPrimes,Finset.mem_insert,Finset.mem_singleton] at f
      rcases f with rfl|rfl
      exact Nat.prime_two
      exact Nat.prime_three
    · obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp r
      exact Nat.prime_of_mem_primeFactors h
  have lb (p : ℕ) (mem : p∈T∪(S\T)) (_ : p∉S) : 1≤p := by
    rcases Finset.mem_union.mp mem with t|h
    · exact (Nat.prime_of_mem_primeFactors t).one_lt.le
    · exact (primeS p (Finset.mem_sdiff.mp h).1).one_lt.le
  have le := Finset.prod_le_prod_of_subset_of_one_le (f:=id) inc lb
  have dis : Disjoint T (S\T) := Finset.disjoint_left.mpr fun _ ht hh => (Finset.mem_sdiff.mp hh).2 ht
  have bound : primeProduct T ≤ 30*d.natAbs := Nat.le_of_dvd (Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hd))
    (Nat.prod_primeFactors_dvd _)
  change (∏ p∈S,p)≤(30*d.natAbs)*(∏ p∈S\T,p)
  exact (by simpa only [id_eq,Finset.prod_union dis] using le : (∏ p∈S,p)≤(∏ p∈T,p)*(∏ p∈S\T,p)).trans
    (Nat.mul_le_mul_right _ bound)

/-- Each extra prime divides exactly one row, to positive even order. -/
theorem extra_order {d : ℤ} {x y : ℚ} (hd : d≠0) (hy : y≠0) (pt : 30*(d:ℚ)*y^2=quintic x)
    {p : ℕ} (mem : p∈extraPrimes d x) :
    p.Prime ∧ ¬p∣30*d.natAbs ∧ ∃! i : Fin 6,
      p∣(row i x.num x.den).natAbs ∧ Even ((row i x.num x.den).natAbs.factorization p) := by
  obtain ⟨s,out⟩ := Finset.mem_sdiff.mp mem
  have d0 : 30*d.natAbs≠0 := mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hd)
  have fixed : fixedPrimes⊆(30*d.natAbs).primeFactors := by
    have pr : (6:ℕ).primeFactors=fixedPrimes := by
      rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide) (by decide),Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
      decide
    rw [←pr]
    exact Nat.primeFactors_mono (dvd_mul_of_dvd_left (by decide : 6∣30) _) d0
  have away : p∉fixedPrimes := fun f => out (fixed f)
  obtain ⟨i,_,hit⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp s).resolve_left away)
  have prime := Nat.prime_of_mem_primeFactors hit
  have nd : ¬p∣30*d.natAbs := fun hp => out (Nat.mem_primeFactors.mpr ⟨prime,hp,d0⟩)
  have off := twist_rows hd hy pt
  have primitive : Int.gcd x.num (x.den:ℤ)=1 := by simpa [Int.gcd] using x.reduced
  have onlyRow (j : Fin 6) (dv : p∣(row j x.num x.den).natAbs) : j=i :=
    unique_form primitive away (Nat.mem_primeFactors.mpr ⟨prime,dv,Int.natAbs_ne_zero.mpr (off _)⟩) hit
  refine ⟨prime,nd,i,⟨Nat.dvd_of_mem_primeFactors hit,?_⟩,fun j h => onlyRow j h.1⟩
  let R (j : Fin 6) := row j x.num x.den
  let F : ℤ := ∏ j,R j
  have e : F=realCubic x.num x.den*imaginaryCubic x.num x.den := by
    simp [F,R,Fin.prod_univ_succ,row,coeffA,coeffB,realCubic,imaginaryCubic]
    ring
  have point : (F:ℚ)=((30*d:ℤ):ℚ)*(y*(x.den:ℚ)^3)^2 := by
    simpa only [e,Int.cast_mul,Int.cast_ofNat] using product_at_twist pt
  let _ : Fact p.Prime := ⟨prime⟩
  have v := congrArg (padicValRat p) point
  have td : ((30*d:ℤ):ℚ)≠0 := by exact_mod_cast (mul_ne_zero (by decide : (30:ℤ)≠0) hd)
  have yn := mul_ne_zero hy (pow_ne_zero 3 (by exact_mod_cast x.den_nz : (x.den:ℚ)≠0))
  rw [padicValRat.mul td (pow_ne_zero _ yn),padicValRat.pow,padicValRat.of_int,padicValRat.of_int,
    padicValInt,padicValInt,←Nat.factorization_def _ prime,←Nat.factorization_def _ prime] at v
  have absF : F.natAbs = ∏ j,(R j).natAbs := by simp [F,Fin.prod_univ_succ,Int.natAbs_mul]
  have rest (j : Fin 6) (_ : j∈Finset.univ) (ne : j≠i) : (R j).natAbs.factorization p=0 :=
    Nat.factorization_eq_zero_of_not_dvd fun dv => ne (onlyRow j dv)
  have vi : F.natAbs.factorization p=(R i).natAbs.factorization p := by
    rw [absF,Nat.factorization_prod_apply (fun j _ => Int.natAbs_ne_zero.mpr (off j))]
    exact Finset.sum_eq_single_of_mem i (Finset.mem_univ _) rest
  rw [vi,Int.natAbs_mul,show (30:ℤ).natAbs=30 by decide,Nat.factorization_eq_zero_of_not_dvd nd] at v
  change Even ((R i).natAbs.factorization p)
  have eqn : (((R i).natAbs.factorization p : ℕ) : ℤ)=2*padicValRat p (y*(x.den:ℚ)^3) := by
    simpa using v
  have evenZ : Even ((((R i).natAbs.factorization p : ℕ) : ℤ)) :=
    ⟨padicValRat p (y*(x.den:ℚ)^3),by linarith only [eqn]⟩
  exact_mod_cast evenZ

/-- A test involving only primes outside the twisting integer. -/
theorem height_of_extra (published : PublishedCorollary72) {d : ℤ} {x y : ℚ}
    (hd : d≠0) (hy : y≠0) (pt : 30*(d:ℚ)*y^2=quintic x)
    (small : 180*extraProduct d x≤100^46*d.natAbs^45) :
    ratHeight x≤10^54*(d.natAbs:ℝ)^24 := by
  apply pooled_height published hd hy pt
  calc
    _ ≤ 6*(30*d.natAbs*extraProduct d x) := Nat.mul_le_mul_left _ (support_split hd x)
    _ = d.natAbs*(180*extraProduct d x) := by ring
    _ ≤ d.natAbs*(100^46*d.natAbs^45) := Nat.mul_le_mul_left _ small
    _ = (100*d.natAbs)^46 := by ring

end
end ZInQBlueprint.SixUnitCharts
#print axioms ZInQBlueprint.SixUnitCharts.support_split
#print axioms ZInQBlueprint.SixUnitCharts.extra_order
#print axioms ZInQBlueprint.SixUnitCharts.height_of_extra
