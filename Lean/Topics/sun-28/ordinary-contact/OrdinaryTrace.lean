import QuadraticAverage
import Mathlib.Tactic

/-! The unnormalized quadratic trace in all sixteen ordinary tests of Sun §4. -/
open Sun28.ScalarTrace
namespace Sun28.Ordinary
variable {K I : Type*} [Field K] [Fintype I]

def weightProduct (r : K) (D : I → K) (k : I → ℕ) :=
  ∏ i, factor r (D i) (k i)

omit [Fintype I] in
private theorem partialWeight (v : AddValuation K (WithTop ℤ)) (r : K)
    (D : I → K) (k : I → ℕ) {α : ℤ} (hr : v r=(α:WithTop ℤ)) (odd : Odd α)
    (S : Finset I) :
    ∃ l : ℤ, v (∏ i ∈ S, factor r (D i) (k i))=(l:WithTop ℤ) ∧ l ≤ 0 ∧
      ∀ i ∈ S, D i=0 ∨ ∃ d : ℤ, v (D i)=(d:WithTop ℤ) ∧ l ≤ α+2*(d-(k i:ℤ)*α) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp,le_rfl,by simp⟩
  | @insert a S hnot ih =>
    obtain ⟨l,hl,hl0,old⟩ := ih
    obtain ⟨m,hm,hm0,fresh⟩ := factor_order (D:=D a) v hr odd (k a)
    refine ⟨m+l,?_,by omega,?_⟩
    · rw [Finset.prod_insert hnot,v.map_mul,hm,hl,WithTop.coe_add]
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hin
      · rcases fresh with hz | ⟨d,hv,hd⟩
        · exact Or.inl hz
        · exact Or.inr ⟨d,hv,by omega⟩
      · rcases old i hin with hz | ⟨d,hv,hd⟩
        · exact Or.inl hz
        · exact Or.inr ⟨d,hv,by omega⟩

/-- Sharp bound for each test at the place selected by the unnormalized trace. -/
theorem trace_one_place (v : AddValuation K (WithTop ℤ)) {r : K} {α : ℤ}
    (D D' : I → K) (k : I → ℕ) (hr : v r=(α:WithTop ℤ)) (odd : Odd α)
    (θ : K) (live : θ≠0) (trace_eq : θ=(weightProduct r D k)⁻¹+(weightProduct r D' k)⁻¹)
    (pole : 0 ≤ v (r/θ^2)) :
    0 < α ∧ ((∀ i, D i=0 ∨ ∃ d : ℤ, v (D i)=(d:WithTop ℤ) ∧ (4*(k i:ℤ)-3)*α+1 ≤ 4*d) ∨
      (∀ i, D' i=0 ∨ ∃ d : ℤ, v (D' i)=(d:WithTop ℤ) ∧ (4*(k i:ℤ)-3)*α+1 ≤ 4*d)) := by
  obtain ⟨l,hl,hl0,ld⟩ := partialWeight v r D k hr odd Finset.univ
  obtain ⟨m,hm,hm0,md⟩ := partialWeight v r D' k hr odd Finset.univ
  change v (weightProduct r D k)=(l:WithTop ℤ) at hl
  change v (weightProduct r D' k)=(m:WithTop ℤ) at hm
  obtain ⟨t,th⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr live)
  have ht := th.symm
  have hmin := v.map_add (weightProduct r D k)⁻¹ (weightProduct r D' k)⁻¹
  rw [←trace_eq,v.map_inv,v.map_inv,hl,hm,←WithTop.LinearOrderedAddCommGroup.coe_neg,
    ←WithTop.LinearOrderedAddCommGroup.coe_neg] at hmin
  rw [ht] at hmin
  have mt : min (-l) (-m) ≤ t := by exact_mod_cast hmin
  have tn : 0 ≤ t := (le_min (by omega) (by omega)).trans mt
  rw [v.map_div,v.map_pow,hr,ht,←WithTop.coe_nsmul] at pole
  have hp : 0 ≤ α-2*t := by exact_mod_cast pole
  have pos : 1 ≤ α-2*t := by obtain ⟨j,hj⟩ := odd; omega
  refine ⟨by omega,?_⟩
  have choose {b : ℤ} {T : I → K} (bt : -b ≤ t)
      (leaf : ∀ i ∈ Finset.univ, T i=0 ∨ ∃ d : ℤ, v (T i)=(d:WithTop ℤ) ∧ b ≤ α+2*(d-(k i:ℤ)*α)) :
      ∀ i, T i=0 ∨ ∃ d : ℤ, v (T i)=(d:WithTop ℤ) ∧ (4*(k i:ℤ)-3)*α+1 ≤ 4*d := by
    intro i
    rcases leaf i (Finset.mem_univ _) with hz | ⟨d,hd,hb⟩
    · exact Or.inl hz
    · exact Or.inr ⟨d,hd,by linarith [hb]⟩
  rcases min_le_iff.mp mt with left|right
  · exact Or.inl (choose left ld)
  · exact Or.inr (choose right md)

variable [CharZero K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]

noncomputable def ordinaryTrace (r : ℚ) (D : I → K) (k : I → ℕ) : ℚ :=
  Algebra.trace ℚ K (weightProduct (algebraMap ℚ K r) D k)⁻¹

theorem ordinaryTrace_eq (σ : K ≃ₐ[ℚ] K) (nontrivial : σ≠1) (r : ℚ) (D : I → K) (k : I → ℕ) :
    algebraMap ℚ K (ordinaryTrace r D k) =
      (weightProduct (algebraMap ℚ K r) D k)⁻¹+(weightProduct (algebraMap ℚ K r) (fun i => σ (D i)) k)⁻¹ := by
  classical
  have card : Fintype.card (K ≃ₐ[ℚ] K)=2 := by
    rw [← Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]
  have pair : ({1,σ} : Finset (K ≃ₐ[ℚ] K))=Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [nontrivial.symm,card]
  rw [ordinaryTrace,trace_eq_sum_automorphisms,←pair]
  simp [nontrivial.symm,weightProduct,factor]

/-- One choice of conjugation works for every test, including zero tests. -/
theorem ordinaryTrace_orders (v : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (r : ℚ) (D : I → K) (k : I → ℕ) (positive : ∀ i, 1 ≤ k i)
    {α : ℤ} (hr : v (algebraMap ℚ K r)=(α:WithTop ℤ)) (odd : Odd α)
    (live : ordinaryTrace r D k≠0) (pole : 0 ≤ v (algebraMap ℚ K (r/(ordinaryTrace r D k)^2))) :
    0 < α ∧ ∃ τ : K ≃ₐ[ℚ] K, ∀ i, (k i : WithTop ℤ) ≤ (v.comap τ.toRingHom) (D i) := by
  have output := trace_one_place v D (fun i => σ (D i)) k hr odd
    (algebraMap ℚ K (ordinaryTrace r D k)) ((map_ne_zero _).mpr live) (ordinaryTrace_eq σ hs r D k)
    (by simpa only [map_div₀,map_pow] using pole)
  obtain ⟨ha,h⟩ := output
  refine ⟨ha,?_⟩
  have lower (i : I) {a : K} (test : a=0 ∨ ∃ d : ℤ, v a=(d:WithTop ℤ) ∧ (4*(k i:ℤ)-3)*α+1 ≤ 4*d) :
      (k i:WithTop ℤ) ≤ v a := by
    rcases test with rfl | ⟨d,hd,bound⟩
    · simp
    · rw [hd]
      have ki := positive i
      have extra := mul_nonneg (show 0 ≤ 4*(k i:ℤ)-3 by omega) (show 0 ≤ α-1 by omega)
      exact WithTop.coe_le_coe.mpr (by nlinarith [extra])
  rcases h with one|other
  · exact ⟨1,fun i => lower i (one i)⟩
  · exact ⟨σ,fun i => lower i (other i)⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.trace_one_place
#print axioms Sun28.Ordinary.ordinaryTrace_eq
#print axioms Sun28.Ordinary.ordinaryTrace_orders
