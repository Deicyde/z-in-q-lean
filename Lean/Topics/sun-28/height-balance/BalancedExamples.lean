import BalancedFamily

namespace Sun28.HeightBalance.Family
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp
noncomputable section

private theorem abs_conductor {t : ℤ} (ht : 100≤t) :
    primeProduct (rows.primes (A t) (B t)) ≤ 210*(B t).natAbs := by
  have nb : B t≠0 := off_marks ht 0
  have nz : (B t).natAbs≠0 := Int.natAbs_ne_zero.mpr nb
  have cover : rows.primes (A t) (B t)=(210*(B t).natAbs).primeFactors := by
    rw [Nat.primeFactors_mul (by decide : (210:ℕ)≠0) nz]
    rfl
  rw [cover]
  exact Nat.le_of_dvd (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero nz)) (Nat.prod_primeFactors_dvd _)

private theorem cubic_bound {t : ℤ} {p : ℕ} (large : 76176<p) (ht : 100≤t) (htp : t≤2400*(p:ℤ)) :
    210*(B t).natAbs≤p^23 := by
  have pp : 76176<(p:ℤ):=by exact_mod_cast large
  have pos : (0:ℤ)<t := by omega
  have a : 0<t-1 := by omega
  have b : 0<2401*t-1:= by omega
  have bp : 0<B t:=mul_pos (mul_pos (mul_pos (by norm_num) pos) a) b
  have t3 : 0≤(p:ℤ)^3 := by positivity
  have f : 76176≤(p:ℤ):=by omega
  have cm : 0≤(p:ℤ)^4 - 210*9604*2400^3 := by
    have lower:=pow_le_pow_left₀ (by decide:(0:ℤ)≤76176) f 4
    norm_num at lower ⊢
    linarith
  have sq := mul_nonneg cm t3
  have bd : B t≤(9604*2400^3)*(p:ℤ)^3 := calc
    B t ≤ (4*(2400*(p:ℤ))*(2400*(p:ℤ)))*(2401*(2400*(p:ℤ))) := by
      unfold B
      exact mul_le_mul (mul_le_mul (by omega) (by omega) a.le (by positivity)) (by omega) b.le (by positivity)
    _ = _ := by ring
  have bh : 210*B t≤(p:ℤ)^7 :=by nlinarith only [bd,sq]
  have eq : ((B t).natAbs:ℤ)=B t:=by rw [Int.natCast_natAbs,abs_of_pos bp]
  have bh' : 210*(B t).natAbs≤p^7:=by exact_mod_cast (by rwa [←eq] at bh : (210:ℤ)*(B t).natAbs≤(p:ℤ)^7)
  exact bh'.trans (Nat.pow_le_pow_right (by omega) (by decide))

/-- The prime chosen for the parameter occurs to order exactly one in the center. -/
theorem prime_contact {p:ℕ} (pr:p.Prime) (large:76176<p) :
    padicValInt p (B (1+2399*(p:ℤ)))=1 := by
  let _ : Fact p.Prime:=⟨pr⟩
  let k:ℤ:=p
  let t:=1+2399*k
  let a:=4*t*2399*(2401*t-1)
  have kpos : 76176<k:=by dsimp [k];exact_mod_cast large
  have tpos : 0<t:=by dsimp [t];omega
  have na:a≠0:=by dsimp [a];exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by norm_num)) (by omega)
  have np:Prime k:=by simpa [k,Int.prime_iff_natAbs_prime] using pr
  have nsmall (j:ℤ) (pos:0<j) (sm:j≤76176) : ¬k∣j:=by
    intro dv;have := Int.le_of_dvd pos dv;omega
  have nt:¬k∣t:=by
    intro dv
    have h:k∣1:=(dvd_add_left (dvd_mul_left k 2399)).mp dv
    exact nsmall 1 (by decide) (by decide) h
  have nf : ¬k∣2401*t-1:=by
    intro dv
    have eq : 2401*t-1=2400+k*(2401*2399):=by dsimp [t];ring
    rw [eq] at dv
    exact nsmall _ (by decide) (by decide) ((dvd_add_left (dvd_mul_right k _)).mp dv)
  have nd : ¬k∣a:=by
    intro z
    rcases np.dvd_or_dvd z with z|z
    · rcases np.dvd_or_dvd z with z|z
      · exact (np.dvd_or_dvd z).elim (nsmall 4 (by decide) (by decide)) nt
      · exact nsmall 2399 (by decide) (by decide) z
    · exact nf z
  rw [show B (1+2399*(p:ℤ))=a*k by unfold B a t k;ring,padicValInt_mul_eq_succ _ na,
    padicValInt.eq_zero_of_not_dvd nd]

theorem prime_family {p:ℕ} (pr:p.Prime) (large:76176<p) (res:p≡1 [MOD 2400]) :
    let t:ℤ:=1+2399*(p:ℤ)
    Int.gcd (A t) (B t)=1 ∧ (∀ i,oldForm i (A t) (B t)≠0) ∧ Covered (A t) (B t) := by
  let t:ℤ:=1+2399*(p:ℤ)
  have m:(2400:ℤ)∣t := by
    obtain ⟨n,hn⟩:=Nat.modEq_iff_dvd.mp res
    exact ⟨1-2399*n,by dsimp [t];push_cast at hn;omega⟩
  have ht : (100:ℤ)≤t:=by dsimp [t];omega
  refine ⟨primitive m,off_marks ht,rows,1,U t,V t,W t,balanced t,?_⟩
  let T:=heightRadical (A t) (B t)
  have outside:p∉oldCutoff:=by
    intro e
    have := Finset.mem_range.mp (Finset.mem_filter.mp e).1
    omega
  have val : padicValInt p (oldForm 0 (A t) (B t))=1:=prime_contact pr large
  have mem:p∈support (A t) (B t) := Finset.mem_union_right _ (mem_oldContactPrimes.mpr
    ⟨pr,outside,0,by rw [val];decide,by rw [val];decide⟩)
  have div:p∣T:=by
    change p∣heightRadical _ _
    rw [←product_support]
    exact Finset.dvd_prod_of_mem id mem
  have pT:p≤T:=Nat.le_of_dvd (Nat.mul_pos pos_cutoff (pos_odd _ _)) div
  exact (abs_conductor ht).trans ((cubic_bound large ht (by dsimp [t];omega)).trans (Nat.pow_le_pow_left pT _))

theorem unbounded_examples (n:ℕ) :
    ∃ a b : ℤ, Int.gcd a b=1 ∧ (∀ i,oldForm i a b≠0) ∧ Covered a b ∧ (n:ℤ)<a := by
  obtain ⟨p,pr,hp,modulus⟩:=Nat.exists_prime_gt_modEq_one (max n 76176) (by decide : (2400:ℕ)≠0)
  have large : 76176<p:= lt_of_le_of_lt (le_max_right _ _) hp
  have result:=prime_family pr large modulus
  let t:ℤ:=1+2399*(p:ℤ)
  refine ⟨A t,B t,result.1,result.2.1,result.2.2,?_⟩
  have np : n<p:=lt_of_le_of_lt (le_max_left _ _) hp
  have ht : (n:ℤ)<t := by dsimp [t];omega
  have ht2 : t≤t^2 := by nlinarith [mul_nonneg (by omega:0≤t-1) (by omega:0≤t)]
  have hu : t≤U t := by unfold U;nlinarith
  have ua : U t≤A t := by unfold A; nlinarith [mul_nonneg (by omega:0≤U t-1) (by omega:0≤U t)]
  omega

end
end Sun28.HeightBalance.Family
#print axioms Sun28.HeightBalance.Family.prime_contact
#print axioms Sun28.HeightBalance.Family.prime_family
#print axioms Sun28.HeightBalance.Family.unbounded_examples
