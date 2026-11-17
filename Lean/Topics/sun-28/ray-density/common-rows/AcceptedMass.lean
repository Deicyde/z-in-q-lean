import CollisionMass

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open private record_of_pattern weight_of_common eventually_guards from NumericalPattern
open scoped Classical
noncomputable section

theorem exact_below {A : Fin 3→ℚ} {d K L κ:ℕ} {H Y:ℝ} {T:Finset ℕ} (a:Record A d H Y)
    (sevenK:7≤K) (fixed:∀ p∈T,p≤K) (aux:∀p∈κ.primeFactors,p≤K)
    (good:∀i:↥(shifts A),commonPrime K K (a.values.value i)) :
    collisions A K L (pair a)=0 ↔ below a T κ L := by
  rw [no_collision]
  constructor
  · intro clean p hp odd seven le
    by_cases base:p≤K
    · exact clean_below a fixed aux good p hp odd seven base
    · let _ : Fact p.Prime:=⟨hp⟩
      have outT:p∉T:=fun m=>base (fixed p m)
      have outAux:p∉κ.primeFactors:=fun m=>base (aux p m)
      exact (signed_record a odd outT outAux).mp (clean p (mem_places.mpr ⟨by omega,le,hp⟩))
  · intro goodL p mem
    obtain ⟨lo,hi,hp⟩:=mem_places.mp mem
    let _ : Fact p.Prime:=⟨hp⟩
    exact (signed_record a (by omega) (fun m=>by have:=fixed p m;omega)
            (fun m=>by have:=aux p m;omega)).mpr (goodL p hp (by omega) (by omega) hi)

theorem eventually_clean_le_main {A : Fin 3 → ℚ} {d K L κ : ℕ} {H Y : ℝ} {T : Finset ℕ}
    (seven : 7≤K) (fixed : ∀ p∈T,p≤K) (aux : ∀p∈κ.primeFactors,p≤K) (w : ℕ→ℕ)
    (short : ∀ ε:ℝ,0<ε→∀ᶠ N:ℕ in atTop,(w N:ℝ)^2≤ε*N) :
    ∀ᶠ N:ℕ in atTop,cleanMass A d K L N (w N)≤ mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N (w N)) := by
  filter_upwards [eventually_guards A H Y w short] with N guards
  let S:=parameterBox d N (w N)
  let wt:=patternWeight A K K
  let U:=S.filter fun q=>collisions A K L q=0 ∧ wt q≠0
  let V:=(box (A:=A) (d:=d) (H:=H) (Y:=Y) N (w N)).filter fun a=>below a T κ L
  have cand (q:ℕ×ℕ) (hq:q∈U) : ∃a∈V,pair a=q ∧ wt q=weight a := by
    obtain ⟨inside,clear,alive⟩:=mem_filter.mp hq
    obtain ⟨inBox,hd⟩:=mem_filter.mp inside
    obtain ⟨hs,hy⟩:=guards q inBox
    obtain ⟨base,rng⟩:=mem_product.mp inBox
    obtain ⟨a,eq,good⟩:=record_of_pattern hd (mem_Icc.mp rng).1 hs hy alive
    have u:a.u=q.1:=congrArg Prod.fst eq
    have v:a.v=q.2:=congrArg Prod.snd eq
    obtain ⟨a',hit,same⟩:=box_covers a (b:=N) (t:=w N) (by have:=(mem_Ioc.mp base).1;omega)
      (u ▸ (mem_Ioc.mp base).2) (v ▸ (mem_Icc.mp rng).2)
    have good' (i:↥(shifts A)) : commonPrime K K (a'.values.value i) := by
      apply (common_iff_clean a' i).mpr
      rw [gaussian_eq_of_pair same]
      exact (common_iff_clean a i).mp (good i)
    have e:=same.trans eq
    exact ⟨a',mem_filter.mpr ⟨hit,(exact_below a' (by omega) fixed aux good').1 (e ▸ clear)⟩,e,
      e ▸ weight_of_common a' good'⟩
  let pick (q:ℕ×ℕ) (hq:q∈U):=(cand q hq).choose
  let im:=U.attach.image (fun q=>pick q.val q.property)
  have sub : im⊆V := by
    rintro _ h;obtain ⟨q,_,rfl⟩:=mem_image.mp h
    exact (cand q q.property).choose_spec.1
  have inj : Function.Injective (fun q:↥U=>pick q.val q.property) := by
    intro a b eq;apply Subtype.ext
    exact (cand a a.property).choose_spec.2.1.symm.trans
      ((congrArg pair eq).trans (cand b b.property).choose_spec.2.1)
  calc
    cleanMass A d K L N (w N)=∑q∈U,wt q := by
      rw [Finset.sum_filter]; apply sum_congr rfl
      intro q _;by_cases ok:collisions A K L q=0 <;> by_cases live:wt q=0 <;> simp [ok,live,wt] at *
    _ = ∑q∈U.attach,wt q.val := (sum_attach ..).symm
    _ = ∑a∈im,weight a := by
      rw [show im=U.attach.image (fun q=>pick q.val q.property) from rfl,
        sum_image (fun _ _ _ _ h=>inj h)]
      exact sum_congr rfl (fun q _=>(cand q q.property).choose_spec.2.2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun a _ _=>(weight_pos a).le)

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.exact_below
#print axioms Sun28.CommonRows.eventually_clean_le_main