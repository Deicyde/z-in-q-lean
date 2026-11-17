import CommonPrimes

namespace Sun28.FinitePattern
open Finset Filter Topology Sun28.SinglePrime Sun28.ContactFactors Sun28.ContactSieve
open Sun28.WeightedSelection ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

/-- The positive-prime von Mangoldt weight on the single chosen rational-prime set. -/
def primeWeight (K L : ℕ) (m : ℤ) : ℝ :=
  if 0 ≤ m ∧ commonPrime K L m.toNat then Real.log (m.toNat : ℝ) else 0

def form (A : Fin 3 → ℚ) (q : ℕ × ℕ) (r : ↥(shifts A)) : ℤ :=
  (q.1 : ℤ) + offset (dilation A) r * (q.2 : ℤ)^2

def patternWeight (A : Fin 3 → ℚ) (K L : ℕ) (q : ℕ × ℕ) : ℝ :=
  ∏ r : ↥(shifts A), primeWeight K L (form A q r)

/-- The numerical polynomial pattern sum. No Gaussian witness or size guard occurs in the box. -/
def patternMass (A : Fin 3 → ℚ) (d K L N W : ℕ) : ℝ :=
  ∑ q ∈ ((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun q : ℕ × ℕ => d ∣ q.2)),
    patternWeight A K L q

private def heightsBound (A : Fin 3 → ℚ) (H : ℝ) :=
  1 + maxCoefficient A + |H| * (dilation A : ℝ)^2

private theorem eventually_guards (A : Fin 3 → ℚ) (H Y : ℝ) (w : ℕ → ℕ)
    (short : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (w N : ℝ)^2 ≤ ε*N) :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ Ioc (N/2) N ×ˢ Icc 1 (w N),
      H < (slope A q.1 q.2 : ℝ) ∧ ∀ i : ↥(shifts A), Y < (form A q i : ℝ) := by
  let B := heightsBound A H
  have absH := abs_nonneg H
  have aux : 0 ≤ |H| * (dilation A : ℝ)^2 := mul_nonneg absH (sq_nonneg _)
  have bp : 0 < B := by dsimp [B,heightsBound]; positivity
  have cb : (maxCoefficient A : ℝ) ≤ B := by dsimp [B,heightsBound]; linarith
  have hd : H * (dilation A : ℝ)^2 ≤ B := by
    dsimp [B,heightsBound]
    have := mul_le_mul_of_nonneg_right (le_abs_self H) (sq_nonneg (dilation A : ℝ))
    linarith [Nat.cast_nonneg (α:=ℝ) (maxCoefficient A)]
  obtain ⟨v₀,hv₀⟩ := exists_nat_gt (4*Y)
  filter_upwards [short (1/(4*B)) (by positivity), eventually_ge_atTop v₀] with N sm large
  intro q mem
  obtain ⟨h1,h2⟩ := mem_product.mp mem
  have lo := (mem_Ioc.mp h1).1
  obtain ⟨vp,vw⟩ := mem_Icc.mp h2
  have low : (N : ℝ) < 2*q.1 := by exact_mod_cast (show N < 2*q.1 by omega)
  have wn := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) q.2) (show (q.2 : ℝ) ≤ w N by exact_mod_cast vw) 2
  have dpos : (0:ℝ) < dilation A := by exact_mod_cast dilation_positive A
  have vpos : (0:ℝ) < q.2 := by exact_mod_cast vp
  have bw : B*(q.2 : ℝ)^2 ≤ (N : ℝ)/4 := by
    apply (mul_le_mul_of_nonneg_left (wn.trans sm) bp.le).trans_eq
    field_simp
  constructor
  · rw [show (slope A q.1 q.2 : ℝ)=(q.1 : ℝ)/((dilation A : ℝ)*q.2)^2 by simp [Sun28.ContactFactors.slope]]
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [mul_pow,←mul_assoc]
    nlinarith only [low,bw,mul_le_mul_of_nonneg_right hd (sq_nonneg (q.2 : ℝ)),Nat.cast_nonneg (α:=ℝ) N]
  · intro i
    have ci : (offset (dilation A) i).natAbs ≤ maxCoefficient A :=
      Finset.le_sup (f := fun i : ↥(shifts A) => (offset (dilation A) i).natAbs) (mem_univ i)
    have neg : -(offset (dilation A) i) ≤ (maxCoefficient A : ℤ) := by
      apply (neg_le_abs _).trans
      simpa only [←Int.natCast_natAbs] using (Int.ofNat_le.mpr ci)
    have bound : -B ≤ (offset (dilation A) i : ℝ) := by
      have off : -((offset (dilation A) i : ℤ) : ℝ) ≤ (maxCoefficient A : ℝ) := by exact_mod_cast neg
      linarith
    have ylt : 4*Y < (N : ℝ) := hv₀.trans_le (by exact_mod_cast large)
    change Y < ((q.1 : ℤ) + offset (dilation A) i * (q.2 : ℤ)^2 : ℤ)
    push_cast
    nlinarith only [low,bw,ylt,mul_le_mul_of_nonneg_right bound (sq_nonneg (q.2 : ℝ))]

private theorem record_of_pattern {A : Fin 3 → ℚ} {K L d : ℕ} {H Y : ℝ} {q : ℕ × ℕ}
    (hd : d ∣ q.2) (vp : 0 < q.2) (hs : H < (slope A q.1 q.2 : ℝ))
    (hy : ∀ i : ↥(shifts A), Y < (form A q i : ℝ))
    (alive : patternWeight A K L q ≠ 0) :
    ∃ a : Record A d H Y, pair a = q ∧ ∀ i : ↥(shifts A), commonPrime K L (a.values.value i) := by
  have z (i : ↥(shifts A)) : 0 ≤ form A q i ∧ commonPrime K L (form A q i).toNat := by
    by_contra fail
    apply alive
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right fail : primeWeight K L (form A q i) = 0)
  let values : PrimeValues A q.1 q.2 := {
    value := fun r => ((q.1 : ℤ) + offset (dilation A) r * (q.2 : ℤ)^2).toNat
    prime := fun r hr => (z ⟨r,hr⟩).2.1
    equation := fun r hr => Int.toNat_of_nonneg (z ⟨r,hr⟩).1 }
  let π i := (z i).2.2.choose
  have ok (i : ↥(shifts A)) := (z i).2.2.choose_spec
  refine ⟨⟨q.1,q.2,values,π,vp,hd,hs,?_,?_⟩,rfl,fun i => (z i).2⟩
  · intro r hr
    have eq := congrArg (fun m : ℤ => (m : ℝ)) (values.equation r hr)
    simpa only [Int.cast_natCast] using (hy ⟨r,hr⟩).trans_eq eq.symm
  · exact ⟨fun i => (ok i).1,fun i => (ok i).2.1,fun i => (ok i).2.2.1⟩

private theorem weight_of_common {A : Fin 3 → ℚ} {K L d : ℕ} {H Y : ℝ}
    (a : Record A d H Y) (good : ∀ i : ↥(shifts A), commonPrime K L (a.values.value i)) :
    patternWeight A K L (pair a) = weight a := by
  unfold patternWeight weight
  apply Finset.prod_congr rfl
  intro i _
  have eq : form A (pair a) i = (a.values.value i : ℤ) := (a.values.equation i i.property).symm
  simp only [primeWeight,eq,Int.natCast_nonneg,Int.toNat_natCast,true_and,ite_eq_left (good i)]

/-- Every surviving summand in the rational-prime pattern sum contributes its exact
weight to the project's finite-cutoff count once the width is short. -/
theorem eventually_pattern_le_main {A : Fin 3 → ℚ} {K L d κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (hT : ∀ p ∈ T,p ≤ K) (hκ : ∀ p ∈ κ.primeFactors,p ≤ K)
    (w : ℕ → ℕ) (short : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (w N : ℝ)^2 ≤ ε*N) :
    ∀ᶠ N : ℕ in atTop, patternMass A d K L N (w N) ≤
      mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N (w N)) := by
  filter_upwards [eventually_guards A H Y w short] with N guards
  let S := (Ioc (N/2) N ×ˢ Icc 1 (w N)).filter fun q : ℕ × ℕ => d ∣ q.2
  let U := S.filter fun q => patternWeight A K L q ≠ 0
  let V := (box (A:=A) (d:=d) (H:=H) (Y:=Y) N (w N)).filter fun a => below a T κ L
  have candidates (q : ℕ × ℕ) (hq : q ∈ U) :
      ∃ a ∈ V, pair a = q ∧ patternWeight A K L q = weight a := by
    obtain ⟨inside,alive⟩ := mem_filter.mp hq
    obtain ⟨inBox,hd⟩ := mem_filter.mp inside
    obtain ⟨hs,hy⟩ := guards q inBox
    obtain ⟨base,vbound⟩ := mem_product.mp inBox
    have vp := (mem_Icc.mp vbound).1
    obtain ⟨a,eq,good⟩ := record_of_pattern hd vp hs hy alive
    have u : a.u = q.1 := congrArg Prod.fst eq
    have v : a.v = q.2 := congrArg Prod.snd eq
    obtain ⟨a',hit,same⟩ := box_covers a (b:=N) (t:=w N) (by have := (mem_Ioc.mp base).1; omega)
      (u ▸ (mem_Ioc.mp base).2) (v ▸ (mem_Icc.mp vbound).2)
    have good' (i : ↥(shifts A)) : commonPrime K L (a'.values.value i) := by
      apply (common_iff_clean a' i).mpr
      rw [gaussian_eq_of_pair same]
      exact (common_iff_clean a i).mp (good i)
    have eq' := same.trans eq
    exact ⟨a', mem_filter.mpr ⟨hit,clean_below a' hT hκ good'⟩,eq',
      eq' ▸ weight_of_common a' good'⟩
  let pick (q : ℕ × ℕ) (hq : q ∈ U) := (candidates q hq).choose
  let image := U.attach.image (fun q => pick q.val q.property)
  have sub : image ⊆ V := by
    intro a mem
    obtain ⟨q,_,rfl⟩ := mem_image.mp mem
    exact (candidates q q.property).choose_spec.1
  have injective : Function.Injective (fun q : ↥U => pick q.val q.property) := by
    intro a b eq
    apply Subtype.ext
    exact (candidates a a.property).choose_spec.2.1.symm.trans
      ((congrArg pair eq).trans (candidates b b.property).choose_spec.2.1)
  change (∑ q ∈ S, patternWeight A K L q) ≤ ∑ a ∈ V,weight a
  calc
    _ = ∑ q ∈ U, patternWeight A K L q := by
      symm; rw [Finset.sum_filter]; apply sum_congr rfl; intro q _
      split <;> simp_all
    _ = ∑ q ∈ U.attach, patternWeight A K L q.val := (Finset.sum_attach ..).symm
    _ = ∑ a ∈ image, weight a := by
      rw [show image = U.attach.image (fun q => pick q.val q.property) from rfl,
        Finset.sum_image (fun a _ b _ eq => injective eq)]
      exact Finset.sum_congr rfl fun q _ => (candidates q q.property).choose_spec.2.2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => (weight_pos a).le)

end
end Sun28.FinitePattern
#print axioms Sun28.FinitePattern.eventually_pattern_le_main
