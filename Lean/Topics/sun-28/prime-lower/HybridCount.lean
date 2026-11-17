import HybridCriterion
import NumericalPattern

namespace Sun28.PrimeLower
open Finset Filter Topology Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection
open Sun28.MediumSieve Sun28.FinitePattern Sun28.NormSieve ManuscriptV15.Arithmetic
open private record_of_pattern weight_of_common eventually_guards from NumericalPattern
open scoped Classical
noncomputable section

/-- Between K and L, at split primes one sign must be absent from all positions.
At inert primes the two rational coordinates alone give the test. -/
def extraTest (A : Fin 3→ℚ) (K L : ℕ) (q : ℕ×ℕ) : Prop :=
  ∃ π : ↥(shifts A) → Gaussian,
    (∀ i, gaussianNorm (π i)=(form A q i).toNat ∧
      gaussianCongruent 16 (π i) (9,0) ∧ gaussianCongruent 7 (π i) (1,3)) ∧
    ∀ p : ℕ,p.Prime → K<p → p≤L →
      if p%4=3 then ¬((q.1 : ZMod p)=1 ∧ (q.2 : ZMod p)=0)
      else (∀ i,¬p∣adjacentNorm (π i) true) ∨ (∀ i,¬p∣adjacentNorm (π i) false)

def hybridWeight (A : Fin 3→ℚ) (K L : ℕ) (q : ℕ×ℕ) : ℝ :=
  if extraTest A K L q then patternWeight A K K q else 0

def hybridMass (A : Fin 3→ℚ) (d K L N W : ℕ) : ℝ :=
   ∑ q ∈ ((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun q : ℕ × ℕ => d ∣ q.2)), hybridWeight A K L q

private theorem test_of_record {A : Fin 3→ℚ} {d K L κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (a : Record A d H Y) (pos : 0<d) (two : 2≤K) (base : exceptionalBound A d ≤ K)
    (fixed : ∀ q∈T,q≤K) (aux : ∀ q∈κ.primeFactors,q≤K)
    (good : ∀ i : ↥(shifts A),commonPrime K K (a.values.value i))
    (test : extraTest A K L (pair a)) : below a T κ L := by
  apply hybrid_below a T pos base fixed aux
  refine ⟨clean_below a fixed aux good,?_⟩
  obtain ⟨π,norms,added⟩ := test
  have eq (i : ↥(shifts A)) : π i=a.gaussian i := by
    obtain ⟨n,h16,h7⟩ := norms i
    have formEq : form A (pair a) i=(a.values.value i:ℤ) := (a.values.equation i i.property).symm
    rw [formEq,Int.toNat_natCast] at n
    exact oriented_unique (a.values.prime i i.property) n (a.rays.norm i) h16 (a.rays.ray16 i) h7 (a.rays.ray7 i)
  intro p pp above endp
  let _ : Fact p.Prime := ⟨pp⟩
  have picked := added p pp above endp
  by_cases i3 : p%4=3
  · simpa [i3,pair] using picked
  · simp only [i3,ite_false] at picked ⊢
    have odd : p≠2 := by omega
    apply (Sun28.MixedSieve.atPrime_iff_fibre a T κ p odd (fun m=>by have:=fixed p m;omega)
      (fun m=>by have:=aux p m;omega)).mpr
    intro obstruction
    obtain ⟨i,j,pl,mi⟩ := (Sun28.MixedSieve.fibre_obstructed_iff a p).mp obstruction
    simp_rw [eq] at picked
    rcases picked with hp|hm
    · exact hp i pl
    · exact hm j mi

theorem hybrid_le_main_of_guards {A : Fin 3→ℚ} {d K L κ N W : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (pos : 0<d) (two : 2≤K) (base : exceptionalBound A d ≤ K)
    (fixed : ∀ q∈T,q≤K) (aux : ∀ q∈κ.primeFactors,q≤K)
    (guards : ∀ q∈Ioc (N/2) N ×ˢ Icc 1 W,
      H < (slope A q.1 q.2 : ℝ) ∧ ∀ i : ↥(shifts A), Y < (form A q i : ℝ)) :
    hybridMass A d K L N W ≤ mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W) := by
  let S := (Ioc (N/2) N ×ˢ Icc 1 W).filter fun q : ℕ × ℕ => d ∣ q.2
  let U := S.filter fun q => hybridWeight A K L q ≠ 0
  let V := (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W).filter fun a => below a T κ L
  have candidates (q : ℕ × ℕ) (hq : q ∈ U) :
      ∃ a ∈ V, pair a = q ∧ hybridWeight A K L q = weight a := by
    obtain ⟨inside,alive⟩ := mem_filter.mp hq
    obtain ⟨inBox,hd⟩ := mem_filter.mp inside
    have test : extraTest A K L q := by
      by_contra h
      exact alive (by simp [hybridWeight,h])
    have old : patternWeight A K K q≠0 := by simpa [hybridWeight,test] using alive
    obtain ⟨hs,hy⟩ := guards q inBox
    obtain ⟨base,vbound⟩ := mem_product.mp inBox
    have vp := (mem_Icc.mp vbound).1
    obtain ⟨a,eq,good⟩ := record_of_pattern hd vp hs hy old
    have u : a.u = q.1 := congrArg Prod.fst eq
    have v : a.v = q.2 := congrArg Prod.snd eq
    obtain ⟨a',hit,same⟩ := box_covers a (b:=N) (t:=W) (by have := (mem_Ioc.mp base).1; omega)
      (u ▸ (mem_Ioc.mp base).2) (v ▸ (mem_Icc.mp vbound).2)
    have good' (i : ↥(shifts A)) : commonPrime K K (a'.values.value i) := by
      apply (common_iff_clean a' i).mpr
      rw [gaussian_eq_of_pair same]
      exact (common_iff_clean a i).mp (good i)
    have eq' := same.trans eq
    have extra : extraTest A K L (pair a') := eq' ▸ test
    refine ⟨a',mem_filter.mpr ⟨hit,test_of_record a' pos two ‹exceptionalBound A d≤K› fixed aux good' extra⟩,eq',?_⟩
    rw [hybridWeight,ite_eq_left test,←eq']
    exact weight_of_common a' good'
  let pick (q : ℕ × ℕ) (hq : q ∈ U) := (candidates q hq).choose
  let image := U.attach.image (fun q => pick q.val q.property)
  have sub : image ⊆ V := by
    intro a mem
    obtain ⟨q,_,rfl⟩ := mem_image.mp mem
    exact (candidates q q.property).choose_spec.1
  have inject : Function.Injective (fun q : ↥U => pick q.val q.property) := by
    intro a b eq
    apply Subtype.ext
    exact (candidates a a.property).choose_spec.2.1.symm.trans
      ((congrArg pair eq).trans (candidates b b.property).choose_spec.2.1)
  change (∑ q ∈ S, hybridWeight A K L q) ≤ ∑ a ∈ V,weight a
  calc
    _ = ∑ q ∈ U,hybridWeight A K L q := by
      symm; rw [Finset.sum_filter]; apply sum_congr rfl; intro q _
      split <;> simp_all
    _ = ∑ q ∈ U.attach, hybridWeight A K L q.val := (Finset.sum_attach ..).symm
    _ = ∑ a ∈ image,weight a := by
      rw [show image = U.attach.image (fun q => pick q.val q.property) from rfl,
        Finset.sum_image (fun a _ b _ e => inject e)]
      exact Finset.sum_congr rfl fun q _ => (candidates q q.property).choose_spec.2.2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => (weight_pos a).le)

theorem eventually_hybrid_le_main {A : Fin 3→ℚ} {d K L κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (pos : 0<d) (two : 2≤K) (base : exceptionalBound A d ≤ K)
    (fixed : ∀ q∈T,q≤K) (aux : ∀ q∈κ.primeFactors,q≤K) (w : ℕ → ℕ)
    (short : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (w N : ℝ)^2 ≤ ε*N) :
    ∀ᶠ N : ℕ in atTop, hybridMass A d K L N (w N) ≤
      mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N (w N)) := by
  filter_upwards [eventually_guards A H Y w short] with N guards
  exact hybrid_le_main_of_guards pos two base fixed aux guards

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.hybrid_le_main_of_guards
#print axioms Sun28.PrimeLower.eventually_hybrid_le_main
