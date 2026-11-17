import FiveMarks

/-! Deleting any one of the five contacts leaves unbounded height at odd radical one. -/
namespace Sun28.FourContact
open Sun28.Ordinary Sun28.FiveMarkTriples Sun28.FiveMarkUnits Height

private theorem valuation_product {p : ℕ} [Fact p.Prime]
    (f : Fin 5 → ℚ) (T : Finset (Fin 5)) (nz : ∀ j∈T, f j≠0) :
    padicValRat p (∏ j∈T,f j)=∑ j∈T,padicValRat p (f j) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have nt : ∀ j∈T,f j≠0 := fun j hj => nz j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,
      padicValRat.mul (nz a (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr nt),ih nt]

private theorem primitive (s : ℚ) : Int.gcd s.num (s.den:ℤ)=1 := by
  simpa [Int.gcd] using s.reduced.gcd_eq_one

/-- The product has even order; the minor computation makes that a separate
even order for each of the four retained forms of the actual primitive pair. -/
theorem retained_even (i : Fin 5) (n : ℕ)
    (off : ∀ j, oldForm j (slope i n).num (slope i n).den≠0)
    {p : ℕ} (prime : p.Prime) (outside : p∉oldCutoff) (j : Fin 5) (keep : j≠i) :
    Even (padicValInt p (oldForm j (slope i n).num (slope i n).den)) := by
  let : Fact p.Prime := ⟨prime⟩
  let s:=slope i n
  let f : Fin 5 → ℤ := fun k => oldForm k s.num s.den
  let U : Finset (Fin 5):= Finset.univ.erase i
  have live (k : Fin 5) : (f k:ℚ)≠0 := by exact_mod_cast off k
  have pn : (∏ k∈U,(f k:ℚ))≠0 := Finset.prod_ne_zero_iff.mpr (fun k _=>live k)
  obtain ⟨t,e⟩:=homogeneous_square i n
  change (∏ k∈U,(f k:ℚ))=(signedTwist i:ℚ)*t^2 at e
  have tn : t≠0 := by intro z;apply pn;rw [e,z];ring
  have Dn : (signedTwist i:ℚ)≠0 := by exact_mod_cast twist_nonzero i
  have large : 76176<p := by
    by_contra! h
    exact outside (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩)
  have unit : padicValRat p (signedTwist i:ℚ)=0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (twist_unit prime large i)
  have eq:=congrArg (padicValRat p) e
  rw [valuation_product _ _ (fun k _=>live k),padicValRat.mul Dn (pow_ne_zero _ tn),
    padicValRat.pow,unit,zero_add] at eq
  change Even (padicValInt p (f j))
  by_cases div : p∣(f j).natAbs
  · have member : p∈formPrimes j s.num s.den :=
      Nat.mem_primeFactors.mpr ⟨prime,div,Int.natAbs_ne_zero.mpr (off j)⟩
    have zero (k : Fin 5) (_ : k∈U) (dist : k≠j) : padicValRat p (f k:ℚ)=0 := by
      have nd : ¬p∣(f k).natAbs :=
        fun h => dist (unique_form (primitive s) outside
          (Nat.mem_primeFactors.mpr ⟨prime,h,Int.natAbs_ne_zero.mpr (off k)⟩) member)
      rw [padicValRat.of_int]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd nd
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨keep,Finset.mem_univ _⟩) zero,
      padicValRat.of_int] at eq
    norm_num at eq
    exact ⟨(padicValInt p (f j))/2, by omega⟩
  · have z : padicValInt p (f j)=0 := padicValNat.eq_zero_of_not_dvd div
    rw [z]; exact ⟨0,rfl⟩

def retainedSupport (i : Fin 5) (A B : ℤ) : Finset ℕ :=
  ((Finset.univ.erase i).biUnion fun j => (oldForm j A B).natAbs.primeFactors.filter
    fun p => Odd (padicValInt p (oldForm j A B))) \ oldCutoff

theorem retainedSupport_empty (i : Fin 5) (n : ℕ)
    (off : ∀ j,oldForm j (slope i n).num (slope i n).den≠0) :
    retainedSupport i (slope i n).num (slope i n).den=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨member,outside⟩:=Finset.mem_sdiff.mp hp
  obtain ⟨j,keep,mem⟩:=Finset.mem_biUnion.mp member
  obtain ⟨fac,odd⟩:=Finset.mem_filter.mp mem
  exact (Nat.not_even_iff_odd.mpr odd) (retained_even i n off
    (Nat.prime_of_mem_primeFactors fac) outside j (Finset.ne_of_mem_erase keep))

private theorem avoids_of_large (s : ℚ) (hs : 10000<logHeight₁ s) :
    ∀ j,oldForm j s.num s.den≠0 := by
  intro j h
  have eq:=primitive_form j s
  rw [h,Int.cast_zero,eq_comm] at eq
  have z : affineForm j s=0 := (mul_eq_zero.mp eq).resolve_left (by exact_mod_cast s.den_nz)
  have bound (t : ℚ) (small : max t.num.natAbs t.den ≤ 10000) : logHeight₁ t≤10000 := by
    rw [Rat.logHeight₁_eq_log_max]
    have pos : 0<(max t.num.natAbs t.den:ℕ) := t.den_pos.trans_le (le_max_right _ _)
    have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast pos : 0<((max t.num.natAbs t.den:ℕ):ℝ))
    have br : ((max t.num.natAbs t.den:ℕ):ℝ)≤10000 := by exact_mod_cast small
    linarith
  fin_cases j <;> norm_num [affineForm] at z
  · exact (not_le_of_gt hs) (z ▸ bound 0 (by decide))
  · have e : s=1 := by linarith
    exact (not_le_of_gt hs) (e ▸ bound 1 (by decide))
  · have e : s=2401 := by linarith
    exact (not_le_of_gt hs) (e ▸ bound 2401 (by decide))
  · have e : s=(-343/32:ℚ) := by linarith
    exact (not_le_of_gt hs) (e ▸ bound (-343/32) (by norm_num))

/-- For any choice of the suppressed row and any real height bound, there is
a primitive point missing all five marks, higher than the bound, with empty
four-contact support outside the paper's own cutoff. -/
theorem four_contacts_insufficient (i : Fin 5) (H : ℝ) :
    ∃ A B : ℤ, Int.gcd A B=1 ∧ (∀ j,oldForm j A B≠0) ∧
      retainedSupport i A B=∅ ∧ H<pairLogHeight A B := by
  have inf:=Set.infinite_range_of_injective (slope_injective i)
  have fin:=NumberField.finite_setOfPred_logHeight₁_le ℚ (max H 10000)
  obtain ⟨n,high⟩ : ∃ n,max H 10000<logHeight₁ (slope i n) := by
    by_contra! bounded
    apply inf (fin.subset ?_)
    rintro _ ⟨n,rfl⟩
    exact bounded n
  let s:=slope i n
  have off:=avoids_of_large s ((le_max_right H 10000).trans_lt high)
  have nb : (s.den:ℤ)≠0 := by exact_mod_cast s.den_nz
  refine ⟨s.num,s.den,primitive s,off,retainedSupport_empty i n off,?_⟩
  rw [←signed_height nb (primitive s)]
  change H<logHeight₁ ((s.num:ℚ)/(s.den:ℚ))
  rw [Rat.num_div_den]
  exact (le_max_left H 10000).trans_lt high

end Sun28.FourContact
#print axioms Sun28.FourContact.retained_even
#print axioms Sun28.FourContact.retainedSupport_empty
#print axioms Sun28.FourContact.four_contacts_insufficient
