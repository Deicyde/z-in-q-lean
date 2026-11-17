import DirectCharts
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The three roots reducing to zero force a forbidden factor t³ in the
constant term of the monic sextic. Multiplicities are retained throughout. -/
namespace ZInQBlueprint.OddContactProduct
open Polynomial IsLocalRing IsDiscreteValuationRing DirectCharts IntegralSextic
noncomputable section

private theorem pow_count_dvd_prod {R k : Type*} [CommRing R] [Zero k] [DecidableEq k]
    (t : R) (ρ : R → k) (s : Multiset R)
    (h : ∀ x ∈ s, ρ x=0 → t ∣ x) : t^((s.map ρ).count 0) ∣ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have htail := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    by_cases ha : ρ a=0
    · simp only [Multiset.map_cons,ha,Multiset.count_cons_self,pow_succ,Multiset.prod_cons]
      simpa only [mul_comm] using mul_dvd_mul (h a (by simp) ha) htail
    · simp only [Multiset.map_cons,Multiset.count_cons_of_ne (Ne.symm ha),Multiset.prod_cons]
      exact dvd_mul_of_dvd_right htail a

/-- The reduction at a nonunit parameter contains X³ over every residue field. -/
theorem reduction {R : Type*} [CommRing R] [IsLocalRing R] {t : R} (ht : residue R t=0) :
    (monicSextic t).map (residue R) = X^3*(X+C 3)^3 := by
  simp only [monicSextic,form,alpha,beta,gamma,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,map_ofNat,
    Polynomial.map_one,Polynomial.map_ofNat,ht,C_0]
  ring

/-- A local divisibility obstruction independent of any choice of uniformizer. -/
theorem not_splits_of_divides {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t : R} (ht : t ≠ 0) (hnu : ¬ IsUnit t) (h₂ : IsUnit (2 : R))
    (hroot : ∀ x : R, (monicSextic t).IsRoot x → residue R x=0 → t ∣ x) :
    ¬ (monicSextic t).Splits := by
  classical
  intro hs
  let f := monicSextic t
  let ρ := residue R
  obtain ⟨hm,hdeg⟩ := monic_six t
  have hρ : residue R t=0 := by
    by_contra h
    exact hnu ((residue_ne_zero_iff_isUnit _).mp h)
  have hred := reduction hρ
  have hmap := hs.roots_map_of_ne_zero (hm.map ρ).ne_zero
  have hn : X^3*(X+C 3)^3 ≠ (0 : (ResidueField R)[X]) := hred ▸ (hm.map ρ).ne_zero
  have hc : 3 ≤ (f.roots.map ρ).count 0 := by
    change 3 ≤ ((monicSextic t).roots.map (residue R)).count 0
    rw [← hmap, hred, roots_mul hn, roots_X_pow, Multiset.count_add,Multiset.nsmul_singleton,
      Multiset.count_replicate_self]
    omega
  have hprod : t^3 ∣ f.roots.prod :=
    (pow_dvd_pow t hc).trans (pow_count_dvd_prod t ρ f.roots (fun x hx => hroot x ((mem_roots hm.ne_zero).mp hx)))
  have hp := hs.coeff_zero_eq_prod_roots_of_monic hm
  rw [hdeg,coeff_zero_eq_eval_zero,monic_eval] at hp
  simp [form,alpha,beta,gamma] at hp
  obtain ⟨c,hc⟩ := hprod
  have he : t^2*(8:R)=t^2*(t*c) := by
    change (monicSextic t).roots.prod = t^3*c at hc
    linear_combination hp+hc
  have hdiv : t ∣ (8:R) := ⟨c,mul_left_cancel₀ (pow_ne_zero _ ht) he⟩
  have hu : IsUnit (8:R) := by convert h₂.pow 3 using 1; norm_num
  exact hnu (isUnit_of_dvd_unit hdiv hu)

theorem not_splits {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {t : R} {n : ℕ} (hn : 0<n) (ht : addVal R t = (n:ℕ∞)) (h₂ : IsUnit (2:R))
    (hroot : ∀ x : R, (monicSextic t).IsRoot x → residue R x=0 → (n:ℕ∞) ≤ addVal R x) :
    ¬ (monicSextic t).Splits := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [addVal_zero] at ht
    simp at ht
  have hnu : ¬IsUnit t := by
    intro u
    rw [addVal_eq_zero_iff.mpr u] at ht
    exact (show (0:ℕ)≠n by omega) (by exact_mod_cast ht)
  apply not_splits_of_divides ht0 hnu h₂
  intro x hx hρ
  exact addVal_le_iff_dvd.mp (ht ▸ hroot x hx hρ)

/-- A root of a monic polynomial in the fraction field of a DVR already lies
in the DVR, by integral closedness. Thus the same obstruction rules out
splitting over the fraction field. -/
theorem not_splits_fraction {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {t : R} {n : ℕ}
    (hn : 0<n) (ht : addVal R t = (n:ℕ∞)) (h₂ : IsUnit (2:R))
    (hroot : ∀ x : R, (monicSextic t).IsRoot x → residue R x=0 → (n:ℕ∞) ≤ addVal R x) :
    ¬ ((monicSextic t).map (algebraMap R K)).Splits := by
  intro hs
  apply not_splits hn ht h₂ hroot
  apply hs.of_splits_map_of_injective (IsFractionRing.injective R K)
  intro x hx
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  refine ⟨monicSextic t, (monic_six t).1, ?_⟩
  rw [eval₂_eq_eval_map]
  exact (mem_roots'.mp hx).2

end
end ZInQBlueprint.OddContactProduct
#print axioms ZInQBlueprint.OddContactProduct.reduction
#print axioms ZInQBlueprint.OddContactProduct.not_splits_of_divides
#print axioms ZInQBlueprint.OddContactProduct.not_splits
#print axioms ZInQBlueprint.OddContactProduct.not_splits_fraction
