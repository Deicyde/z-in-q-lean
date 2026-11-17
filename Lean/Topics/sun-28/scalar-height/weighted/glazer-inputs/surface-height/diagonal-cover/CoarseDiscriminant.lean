import CoverField
import CoverRamification
import InertialRoots
import Divisibility
import ScalarOctic

namespace ZInQBlueprint.Diagonal210
open Polynomial IntermediateField NumberField Sun28.FiveDescent.ResidueField Sun28.Ordinary
open scoped NumberField
noncomputable section

instance coordinateNumberField {s : ℚ} (y : Fibre ℂ coefficient s) : NumberField (rootField y) where
  to_charZero := inferInstance
  to_finiteDimensional := finite_rootField y

/-- A compositum of the splitting fields of the four quadratic polynomials. -/
theorem coordinate_galois {s : ℚ} (y : Fibre ℂ coefficient s) : IsGalois ℚ (rootField y) := by
  let f (i : Fin 4) : ℚ[X] := X^2-C (radicand s i)
  let T (i : Fin 4) := adjoin ℚ ((f i).rootSet ℂ)
  have normal (i : Fin 4) : Normal ℚ (T i) :=
    Normal.of_isSplittingField (f i) (hFEp := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _))
  have zeros (i : Fin 4) (z : ℂ) : z∈(f i).rootSet ℂ ↔ z^2=algebraMap ℚ ℂ (radicand s i) := by
    rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero (by decide : 0<2) _)]
    simp [sub_eq_zero]
  have eqn : rootField y=⨆ i,T i := by
    apply le_antisymm
    · apply adjoin_le_iff.mpr
      rintro _ ⟨i,rfl⟩
      exact le_iSup T i (subset_adjoin _ _ ((zeros i _).mpr (y.2 i)))
    · apply iSup_le
      intro i
      apply adjoin_le_iff.mpr
      intro z hz
      have e := ((zeros i z).mp hz).trans (y.2 i).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h|h
      · rw [h]; exact (generator y i).property
      · rw [h]; exact (rootField y).neg_mem (generator y i).property
  have n : Normal ℚ (rootField y) := by
    rw [eqn]
    infer_instance
  exact { to_normal := n }

private theorem signed_part (q : ℚ) (qn : q≠0) :
    ∃ (d : ℤ) (v : ℚ), Squarefree d ∧ v≠0 ∧ q=(d:ℚ)*v^2 := by
  have de : (q.den:ℚ)≠0 := by exact_mod_cast q.den_nz
  have num := Rat.num_div_den q
  obtain ⟨a,d,h,sd⟩ := exists_sq_mul_squarefree (q.num*(q.den:ℤ))
  have cast : (a:ℚ)^2*(d:ℚ)=(q.num:ℚ)*(q.den:ℚ) := by exact_mod_cast h
  have eq : q=(d:ℚ)*((a:ℚ)/q.den)^2 := by
    conv_lhs => rw [←num]
    field_simp
    linear_combination -cast
  refine ⟨d,(a:ℚ)/q.den,sd,?_,eq⟩
  intro e
  exact qn (by simpa [e] using eq)

/-- For an odd rational prime, the coarse discriminant has exactly the support
of the four odd valuations, including when some quadratic extensions coincide. -/
theorem coordinate_discriminant {s : ℚ} (y : Fibre ℂ coefficient s) (nonzero : ∀ i,radicand s i≠0)
    {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) :
    (p:ℤ)∣NumberField.discr (rootField y) ↔ ∃ i,Odd (padicValRat p (radicand s i)) := by
  let L := rootField y
  let : IsGalois ℚ L := coordinate_galois y
  choose d v sd vn eq using fun i=>signed_part _ (nonzero i)
  let z (i : Fin 4) : L := generator y i/algebraMap ℚ L (v i)
  have roots (i : Fin 4) : (z i)^2=(d i:L) := by
    dsimp only [z]
    rw [div_pow,generator_sq,eq,map_mul,map_pow,map_intCast]
    change (d i:L)*(algebraMap ℚ L (v i))^2/(algebraMap ℚ L (v i))^2=(d i:L)
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 ((map_ne_zero (algebraMap ℚ L)).mpr (vn i)))
  have support (i : Fin 4) : p∣(d i).natAbs ↔ Odd (padicValRat p (radicand s i)) := by
    have dn : (d i:ℚ)≠0 := fun e=>nonzero i (by rw [eq,e,zero_mul])
    rw [ZInQBlueprint.OddSupport.squarefree_odd_order (sd i),eq,padicValRat.mul dn (pow_ne_zero 2 (vn i)),padicValRat.pow]
    simp only [Int.odd_iff]
    push_cast
    omega
  constructor
  · intro divides
    by_contra! miss
    have pr := Nat.prime_iff_prime_int.mp hp.out
    let I : Ideal ℤ := Ideal.span {(p:ℤ)}
    have : I.IsPrime := (Ideal.span_singleton_prime pr.ne_zero).mpr pr
    refine (show ¬(p:ℤ)∣NumberField.discr L from ?_) divides
    apply (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) pr).mpr
    intro P hP above
    let : P.IsMaximal := hP
    let : P.LiesOver I := above
    have out {a : ℤ} (h : ¬(p:ℤ)∣a) : (a:𝓞 L)∉P :=
      fun mem=>h (Ideal.mem_span_singleton.mp ((Ideal.mem_of_liesOver P I a).mpr mem))
    have p2 : ¬(p:ℤ)∣2 := fun h=>odd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (by exact_mod_cast h))
    have tr : P.inertia (L ≃ₐ[ℚ] L)=⊥ := by
      apply le_antisymm _ bot_le
      intro σ hσ
      rw [Subgroup.mem_bot]
      apply AlgEquiv.coe_toAlgHom_injective
      apply IntermediateField.adjoin_algHom_ext
      rintro _ ⟨i,rfl⟩
      change σ (generator y i)=generator y i
      let u : 𝓞 L := ⟨z i,integral_root (roots i)⟩
      have hnon : ¬(p:ℤ)∣d i := fun h=>miss i ((support i).mp (by simpa using Int.natAbs_dvd_natAbs.mpr h))
      have hfix := inertia_root P σ hσ (u:=u) (a:=d i) (Subtype.ext (roots i)) (by simpa using out p2) (out hnon)
      change σ (generator y i/algebraMap ℚ L (v i))=generator y i/algebraMap ℚ L (v i) at hfix
      have divmap := map_div₀ σ (generator y i) (algebraMap ℚ L (v i))
      have same := divmap.symm.trans hfix
      rw [σ.commutes] at same
      exact (div_left_inj' ((map_ne_zero (algebraMap ℚ L)).mpr (vn i))).mp same
    apply Ideal.ramificationIdx_eq_one_iff.mp
    rw [←Ideal.ramificationIdxIn_eq_ramificationIdx I P (L ≃ₐ[ℚ] L),
      ←Ideal.card_inertia_eq_ramificationIdxIn (G:=L ≃ₐ[ℚ] L) I P,tr]
    simp
  · rintro ⟨i,h⟩
    exact prime_dvd_discr (sd i) (roots i) hp.out ((support i).mpr h)

/-- Ramification of the actual rational fibre field at every prime above the fixed cutoff. -/
theorem discriminant_iff_contact {p : ℕ} [Fact p.Prime] (large : 7<p) {A B : ℤ}
    (cop : Int.gcd A B=1) (hn : ∀ i,oldForm i A B≠0) (y : Fibre ℂ coefficient ((A:ℚ)/B))
    (S : Finset ℕ) (out : p∉S) :
    (p:ℤ)∣NumberField.discr (rootField y) ↔ p∈oldContactPrimes S A B := by
  have bn : B≠0 := by simpa [oldForm] using hn 0
  have bq : (B:ℚ)≠0 := by exact_mod_cast bn
  have nz (i : Fin 4) : radicand ((A:ℚ)/B) i≠0 := by
    rw [affine_radicand A B bn]
    exact div_ne_zero (mul_ne_zero (by fin_cases i <;> norm_num [localUnit]) (by exact_mod_cast hn i.succ)) bq
  exact (coordinate_discriminant y nz (by omega)).trans (odd_radicand_iff_contact large cop hn S out)

/-- Equality of finite prime sets for the cutoff in the original height estimate. -/
theorem discriminant_support {A B : ℤ} (cop : Int.gcd A B=1) (hn : ∀ i,oldForm i A B≠0)
    (y : Fibre ℂ coefficient ((A:ℚ)/B)) :
    (NumberField.discr (rootField y)).natAbs.primeFactors \ oldCutoff = oldContactPrimes oldCutoff A B := by
  have dn := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (rootField y))
  ext p
  by_cases out : p ∈ oldCutoff
  · simp [out,mem_oldContactPrimes]
  · rw [Finset.mem_sdiff]
    by_cases pr : p.Prime
    · have f : Fact p.Prime := ⟨pr⟩
      have big : 7<p := by
        by_contra! small
        exact out (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),pr⟩)
      rw [Nat.mem_primeFactors_of_ne_zero dn]
      have eqv := discriminant_iff_contact big cop hn y oldCutoff out
      have cast : p∣(NumberField.discr (rootField y)).natAbs ↔ (p:ℤ)∣NumberField.discr (rootField y) := by
        simpa using (Int.natAbs_dvd_natAbs (a:=(p:ℤ)) (b:=NumberField.discr (rootField y)))
      simpa [pr,out,cast] using eqv
    · simp [Nat.mem_primeFactors,pr,mem_oldContactPrimes]

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.coordinate_galois
#print axioms ZInQBlueprint.Diagonal210.coordinate_discriminant
#print axioms ZInQBlueprint.Diagonal210.discriminant_iff_contact
#print axioms ZInQBlueprint.Diagonal210.discriminant_support
