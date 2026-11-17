import SixEvenSupport

/-! The exact radical of the six branch forms on a signed squarefree twist. -/
namespace ZInQBlueprint.SixUnitCharts
open Sun28.FiveMarkUnits ZInQ ZInQBlueprint.OddSupport ZInQBlueprint.TwistDescent
noncomputable section

/-- Modulo five the six row directions exhaust the projective line. -/
theorem five_row {a b : ℤ} (off : ∀ i, row i a b ≠ 0) :
    5 ∈ rowSupport Finset.univ a b := by
  have directions : ∀ u v : ZMod 5, ∃ i : Fin 6, (coeffA i : ZMod 5)*u+(coeffB i : ZMod 5)*v=0 := by decide
  obtain ⟨i,hi⟩ := directions a b
  have hit : (5:ℤ) ∣ row i a b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by simpa [row] using hi)
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
    Nat.mem_primeFactors.mpr ⟨by decide,by simpa using Int.natAbs_dvd_natAbs.mpr hit,
      Int.natAbs_ne_zero.mpr (off i)⟩⟩)

/-- A twist prime away from 30 has odd order in the integral product of the six rows. -/
theorem twist_prime_mem {d : ℤ} {x y : ℚ} (sf : Squarefree d) (hy : y≠0)
    (pt : 30*(d:ℚ)*y^2=quintic x) {p : ℕ} (pr : p.Prime) (pd : p∣d.natAbs)
    (away : ¬p∣30) : p∈rowSupport Finset.univ x.num x.den := by
  have off := twist_rows sf.ne_zero hy pt
  let R (i : Fin 6) := row i x.num x.den
  let F : ℤ := ∏ i,R i
  have e : F=realCubic x.num x.den*imaginaryCubic x.num x.den := by
    simp [F,R,Fin.prod_univ_succ,row,coeffA,coeffB,realCubic,imaginaryCubic]
    ring
  have point : (F:ℚ)=((30*d:ℤ):ℚ)*(y*(x.den:ℚ)^3)^2 := by
    simpa only [e,Int.cast_mul,Int.cast_ofNat] using product_at_twist pt
  let _ : Fact p.Prime := ⟨pr⟩
  have v := congrArg (padicValRat p) point
  have td : ((30*d:ℤ):ℚ)≠0 := by exact_mod_cast mul_ne_zero (by decide : (30:ℤ)≠0) sf.ne_zero
  have yn := mul_ne_zero hy (pow_ne_zero 3 (by exact_mod_cast x.den_nz : (x.den:ℚ)≠0))
  rw [padicValRat.mul td (pow_ne_zero _ yn),padicValRat.pow,padicValRat.of_int,padicValRat.of_int,
    padicValInt,padicValInt,←Nat.factorization_def _ pr,←Nat.factorization_def _ pr,Int.natAbs_mul,
    show (30:ℤ).natAbs=30 by decide,Nat.factorization_mul (by decide) (Int.natAbs_ne_zero.mpr sf.ne_zero),
    Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd away,
    Nat.factorization_eq_one_of_squarefree (Int.squarefree_natAbs.mpr sf) pr pd] at v
  by_contra miss
  have vzero (i : Fin 6) : (R i).natAbs.factorization p=0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    exact miss (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Nat.mem_primeFactors.mpr ⟨pr,h,Int.natAbs_ne_zero.mpr (off i)⟩⟩))
  have nf : F.natAbs=∏ i,(R i).natAbs := by simp [F,Fin.prod_univ_succ,Int.natAbs_mul]
  have fzero : F.natAbs.factorization p = 0 := by
    rw [nf,Nat.factorization_prod_apply (fun j _ => Int.natAbs_ne_zero.mpr (off j))]
    exact Finset.sum_eq_zero fun i _ => vzero i
  rw [fzero] at v
  norm_num at v
  omega

private theorem thirty_squarefree : Squarefree (30 : ℕ) := by
  change Squarefree (2*(3*5) : ℕ)
  rw [Nat.squarefree_mul (by decide),Nat.squarefree_mul (by decide)]
  exact ⟨Nat.prime_two.squarefree,Nat.prime_three.squarefree,(by decide : Nat.Prime 5).squarefree⟩

private theorem thirty_factors : (30:ℕ).primeFactors=({2,3,5}:Finset ℕ) := by
  rw [show (30:ℕ)=2*(3*5) by decide,Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_mul (by decide) (by decide),Nat.prime_two.primeFactors,Nat.prime_three.primeFactors,
    (by decide : Nat.Prime 5).primeFactors]
  decide

/-- Every prime factor of the twisting integer or of 30 occurs in the full support. -/
theorem twist_factors_subset {d : ℤ} {x y : ℚ} (sf : Squarefree d) (hy : y≠0)
    (pt : 30*(d:ℚ)*y^2=quintic x) :
    (30*d.natAbs).primeFactors ⊆ rowSupport Finset.univ x.num x.den := by
  have inc : (30:ℕ).primeFactors ⊆ rowSupport Finset.univ x.num x.den := by
    rw [thirty_factors]
    intro p h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl
    · exact Finset.mem_union_left _ (by decide)
    · exact Finset.mem_union_left _ (by decide)
    · exact five_row (twist_rows sf.ne_zero hy pt)
  rw [Nat.primeFactors_mul (by decide) (Int.natAbs_ne_zero.mpr sf.ne_zero)]
  intro p h
  rcases Finset.mem_union.mp h with h|h
  · exact inc h
  · by_cases dv : p∣30
    · exact inc (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors h,dv,by decide⟩)
    · exact twist_prime_mem sf hy pt (Nat.prime_of_mem_primeFactors h) (Nat.dvd_of_mem_primeFactors h) dv

/-- The full six-row radical, with the exact overlap at the three small primes. -/
theorem support_exact {d : ℤ} {x y : ℚ} (sf : Squarefree d) (hy : y≠0)
    (pt : 30*(d:ℚ)*y^2=quintic x) :
    primeProduct (rowSupport Finset.univ x.num x.den)=
      30*(d.natAbs/Nat.gcd d.natAbs 30)*extraProduct d x := by
  let D := d.natAbs
  let t := (30*D).primeFactors
  let s := rowSupport Finset.univ x.num x.den
  have sub : t⊆s := twist_factors_subset sf hy pt
  have hs : Squarefree D := Int.squarefree_natAbs.mpr sf
  have gd : Squarefree (D.gcd 30) := hs.squarefree_of_dvd (Nat.gcd_dvd_left D 30)
  have h := Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul 30 D (fun p => p)
  rw [Nat.gcd_comm 30 D,Nat.prod_primeFactors_of_squarefree gd,
      Nat.prod_primeFactors_of_squarefree thirty_squarefree,Nat.prod_primeFactors_of_squarefree hs] at h
  have gpos : 0<D.gcd 30 := Nat.gcd_pos_of_pos_right _ (by decide)
  have back : (D/D.gcd 30)*D.gcd 30=D := Nat.div_mul_cancel (Nat.gcd_dvd_left D 30)
  have rad : primeProduct t=30*(D/D.gcd 30) := by
    apply Nat.eq_of_mul_eq_mul_left gpos
    change (D.gcd 30)*(∏ p∈(30*D).primeFactors,p)=(D.gcd 30)*(30*(D/D.gcd 30))
    calc
      _ = 30*D := h
      _ = 30*((D/D.gcd 30)*D.gcd 30) := congrArg (30*·) back.symm
      _ = _ := by ring
  have split := Finset.prod_sdiff (f:=fun p : ℕ=>p) sub
  change primeProduct (s\t)*primeProduct t=primeProduct s at split
  change primeProduct s=30*(D/D.gcd 30)*primeProduct (s\t)
  rw [←split,rad,mul_comm]

/-- The exact numerical test obtained by pooling complementary triples. -/
theorem pooled_test_iff_exact {d : ℤ} {x y : ℚ} (sf : Squarefree d) (hy : y≠0)
    (pt : 30*(d:ℚ)*y^2=quintic x) :
    6*primeProduct (rowSupport Finset.univ x.num x.den)≤(100*d.natAbs)^46 ↔
      180*extraProduct d x≤100^46*d.natAbs^45*Nat.gcd d.natAbs 30 := by
  rw [support_exact sf hy pt]
  let D := d.natAbs
  let g := D.gcd 30
  let m := D/g
  have dp : 0<D := Int.natAbs_pos.mpr sf.ne_zero
  have back : m*g=D := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have mp : 0 < m := by
    by_contra! h
    have z : m=0 := Nat.eq_zero_of_le_zero h
    rw [z,zero_mul] at back
    omega
  have left : 6*(30*m*extraProduct d x)=m*(180*extraProduct d x) := by ring
  have right : (100*D)^46=m*(100^46*D^45*g) := by
    calc
      _ = D*(100^46*D^45) := by ring
      _ = (m*g)*(100^46*D^45) := congrArg (·*(100^46*D^45)) back.symm
      _ = _ := by ring
  change 6*(30*m*extraProduct d x)≤(100*D)^46 ↔ 180*extraProduct d x≤100^46*D^45*g
  rw [left,right]
  exact mul_le_mul_iff_right₀ mp

/-- The larger allowance for even-contact primes on every signed squarefree twist. -/
theorem height_of_extra_exact (published : PublishedCorollary72) {d : ℤ} {x y : ℚ}
    (sf : Squarefree d) (hy : y≠0) (pt : 30*(d:ℚ)*y^2=quintic x)
    (small : 180*extraProduct d x≤100^46*d.natAbs^45*Nat.gcd d.natAbs 30) :
    ratHeight x≤10^54*(d.natAbs:ℝ)^24 :=
  pooled_height published sf.ne_zero hy pt ((pooled_test_iff_exact sf hy pt).mpr small)

end
end ZInQBlueprint.SixUnitCharts
#print axioms ZInQBlueprint.SixUnitCharts.five_row
#print axioms ZInQBlueprint.SixUnitCharts.twist_prime_mem
#print axioms ZInQBlueprint.SixUnitCharts.twist_factors_subset
#print axioms ZInQBlueprint.SixUnitCharts.support_exact
#print axioms ZInQBlueprint.SixUnitCharts.pooled_test_iff_exact
#print axioms ZInQBlueprint.SixUnitCharts.height_of_extra_exact
