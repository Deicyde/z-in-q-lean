import BoundedSeparator
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Rationality of separating values on finite Galois-stable solution sets. -/
open Polynomial Finset
namespace ZInQBlueprint.SunTower
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- The geometric solution set is preserved by every automorphism over the base field. -/
def Stable (K : Type*) [Field K] [Algebra K L] (S : Finset (Fin n → L)) : Prop :=
  ∀ (σ : L ≃ₐ[K] L) (x : Fin n → L), x ∈ S → (fun i => σ (x i)) ∈ S

/-- The polynomial with one linear factor for every geometric tuple, prior to descent. -/
def projection (S : Finset (Fin n → L)) (b : ℕ) : L[X] :=
  ∏ x ∈ S, (X - C (separator (b:L) x))

private theorem maps_separator (σ : L ≃ₐ[K] L) (b : ℕ) (x : Fin n → L) :
    σ (separator (b:L) x) = separator (b:L) (fun i => σ (x i)) := by simp [separator]

/-- Every coefficient of the product over a stable set descends to K. -/
theorem projection_lifts [IsGalois K L] {S : Finset (Fin n → L)}
    (hS : Stable K S) (b : ℕ) : ∃ p : K[X], p.map (algebraMap K L) = projection S b := by
  classical
  apply (mem_lifts _).mp
  apply (lifts_iff_coeff_lifts _).mpr
  intro j
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  have perm : (projection S b).map σ.toRingHom = projection S b := by
    unfold projection
    rw [Polynomial.map_prod]
    apply Finset.prod_bij' (fun x _ i => σ (x i)) (fun x _ i => σ.symm (x i))
    · exact fun x hx => hS σ x hx
    · exact fun x hx => hS σ.symm x hx
    · intro x _; funext i; exact σ.symm_apply_apply _
    · intro x _; funext i; exact σ.apply_symm_apply _
    · intro x _; simp [maps_separator]
  have hc := congrArg (fun q : L[X] => q.coeff j) perm
  change ((projection S b).map σ.toRingHom).coeff j = _ at hc
  rw [coeff_map] at hc
  exact hc

/-- A rational separating value occurs precisely at a tuple of rational coordinates. -/
theorem rational_tuple_of_separating [IsGalois K L] {S : Finset (Fin n → L)}
    (hS : Stable K S) {b : ℕ} (hi : Set.InjOn (separator (b:L)) (S : Set (Fin n → L)))
    {x : Fin n → L} (hx : x ∈ S) (r : K) (hr : separator (b:L) x = algebraMap K L r) :
    ∃ y : Fin n → K, (fun i => algebraMap K L (y i)) = x := by
  have h (i : Fin n) : x i ∈ Set.range (algebraMap K L) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    have he : separator (b:L) (fun j => σ (x j)) = separator (b:L) x := by
      rw [← maps_separator,hr,σ.commutes]
    exact congrFun (hi (hS σ x hx) hx he) i
  choose y hy using h
  exact ⟨y,funext hy⟩

/-- Uniform degree and separator budget for the rational-point projection, including the
empty fiber. Over K=ℚ the extra rational variable is a root of p. -/
theorem exists_rational_root_iff [CharZero L] [IsGalois K L] {S : Finset (Fin n → L)}
    (hS : Stable K S) :
    ∃ (b : ℕ) (p : K[X]), b ≤ S.card.choose 2*(n-1) ∧ p.Monic ∧ p.natDegree = S.card ∧
      p.map (algebraMap K L) = projection S b ∧
      ((∃ z : K, p.IsRoot z) ↔ ∃ y : Fin n → K, (fun i => algebraMap K L (y i)) ∈ S) := by
  classical
  obtain ⟨b,hb,hi⟩ := exists_bounded_separator S
  obtain ⟨p,hp⟩ := projection_lifts hS b
  have hm : p.Monic := by
    apply (monic_map_iff (f := algebraMap K L)).mp
    rw [hp]
    exact monic_prod_X_sub_C _ S
  have hd : p.natDegree = S.card := by
    rw [← natDegree_map_eq_of_injective (algebraMap K L).injective p,hp]
    exact natDegree_finsetProd_X_sub_C_eq_card _ _
  refine ⟨b,p,hb,hm,hd,hp,?_⟩
  have eval_at (z : K) : p.IsRoot z ↔ ∃ x ∈ S, separator (b:L) x = algebraMap K L z := by
    change p.eval z = 0 ↔ _
    rw [← (algebraMap K L).injective.eq_iff, map_zero, ← eval_map_apply,hp]
    simp only [projection,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,sub_eq_zero]
    exact exists_congr fun x => and_congr_right fun _ => eq_comm
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨x,hx,he⟩ := (eval_at z).mp hz
    obtain ⟨y,hy⟩ := rational_tuple_of_separating hS hi hx z he
    exact ⟨y,hy ▸ hx⟩
  · rintro ⟨y,hy⟩
    refine ⟨separator (b:K) y,(eval_at _).mpr ⟨_,hy,?_⟩⟩
    simp [separator]

end
end ZInQBlueprint.SunTower
#print axioms ZInQBlueprint.SunTower.projection_lifts
#print axioms ZInQBlueprint.SunTower.rational_tuple_of_separating
#print axioms ZInQBlueprint.SunTower.exists_rational_root_iff
