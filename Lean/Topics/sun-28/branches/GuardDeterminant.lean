import RootMask
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! A fixed Sylvester determinant for rejecting roots at which a guard vanishes.
The outer polynomial before taking the resultant is in Z; the target is R[T][U]. -/
namespace Sun28.Mask
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

/-- Embed the coefficient ring into the bivariate polynomial ring R[T][U]. -/
def embed : R →+* (R[X])[X] := C.comp C

def expression (G : R[X]) : ((R[X])[X])[X] :=
  C X + G.map embed * (C (C X) - X)

/-- All degree bounds are fixed before applying the ring homomorphism to the
parameter values, even if the leading coefficient of G becomes zero. -/
def determinant (P G : R[X]) : (R[X])[X] :=
  resultant (P.map embed) (expression G) P.natDegree (G.natDegree + 1)

private theorem expression_bound (G : R[X]) :
    (expression G).natDegree ≤ G.natDegree + 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · apply natDegree_mul_le.trans
    exact Nat.add_le_add natDegree_map_le ((natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le))

private theorem expression_eval {L : Type*} [Field L] (g : L[X]) (r : L) :
    (expression g).eval (embed r) = factor r (g.eval r) := by
  simp only [expression,eval_add,eval_C,eval_mul,eval_sub,eval_X,eval_map_apply,factor]
  simp [embed]

/-- The Sylvester determinant specializes to the geometric product, with all
root multiplicities. -/
theorem determinant_product {L : Type*} [Field L] (P G : L[X]) (hp : P.Monic)
    (hs : P.Splits) : determinant P G = product P.roots G.eval := by
  have hs' := hs.map (embed (R:=L))
  rw [determinant,← hp.natDegree_map (embed (R:=L)),resultant_eq_prod_eval _ _ _ (expression_bound G) hs',
    (hp.map _).leadingCoeff,one_pow,one_mul,hs.roots_map_of_ne_zero (hp.map _).ne_zero]
  apply congrArg Multiset.prod
  simp only [Multiset.map_map,Function.comp_def,expression_eval]

/-- Map all bivariate coefficients without changing the variables T,U. -/
def mapTU {S : Type*} [CommRing S] (φ : R →+* S) : (R[X])[X] →+* (S[X])[X] :=
  mapRingHom (mapRingHom φ)

private theorem embed_natural {S : Type*} [CommRing S] (φ : R →+* S) :
    (mapTU φ).comp embed = embed.comp φ := by
  ext r
  simp [embed,mapTU]

private theorem expression_map {S : Type*} [CommRing S] (φ : R →+* S) (G : R[X]) :
    (expression G).map (mapTU φ) = expression (G.map φ) := by
  have h : (G.map embed).map (mapTU φ) = (G.map φ).map embed := by
    rw [Polynomial.map_map,Polynomial.map_map,embed_natural]
  simp [expression,h,mapTU] at *

/-- One fixed determinant over the parameter ring works in every geometric
fiber. Its coefficient of lowest U-degree cuts out the retained roots. -/
theorem specialize_product {L : Type*} [Field L] (φ : R →+* L) (P G : R[X])
    (hp : P.Monic) (hs : (P.map φ).Splits) :
    mapTU φ (determinant P G) = product (P.map φ).roots (G.map φ).eval := by
  let p := P.map φ
  let g := G.map φ
  have hleft : (P.map embed).map (mapTU φ) = p.map embed := by
    rw [Polynomial.map_map,embed_natural]
    exact (Polynomial.map_map ..).symm
  have bound : (expression g).natDegree ≤ G.natDegree + 1 :=
    (expression_bound g).trans (Nat.add_le_add_right natDegree_map_le 1)
  have hd : (p.map embed).natDegree = P.natDegree :=
    ((hp.map φ).natDegree_map _).trans (hp.natDegree_map φ)
  have rootMap := hs.roots_map_of_ne_zero ((hp.map φ).map (embed (R:=L))).ne_zero
  unfold determinant
  rw [← resultant_map_map,hleft,expression_map,← hd,
    resultant_eq_prod_eval _ _ _ bound (hs.map _),((hp.map φ).map _).leadingCoeff,one_pow,one_mul,rootMap]
  apply congrArg Multiset.prod
  simp only [Multiset.map_map,Function.comp_def,expression_eval,g]

/-- At a rational specialization, there is a finite coefficient stratum on
which one univariate polynomial has precisely the rational roots passing G. -/
theorem rational_specialization (φ : R →+* ℚ) (P G : R[X]) (hp : P.Monic) :
    ∃ e ≤ P.natDegree,
      (∀ j < e, ((determinant P G).coeff j).map φ = 0) ∧
      ((determinant P G).coeff e).map φ ≠ 0 ∧
      ∀ t : ℚ, (((determinant P G).coeff e).map φ).IsRoot t ↔
        (P.map φ).IsRoot t ∧ ¬(G.map φ).IsRoot t := by
  classical
  let L := AlgebraicClosure ℚ
  let ι := algebraMap ℚ L
  let ψ := ι.comp φ
  have hpψ := hp.map ψ
  have hh := specialize_product ψ P G hp (IsAlgClosed.splits _)
  let e := rejected (P.map ψ).roots (G.map ψ).eval
  obtain ⟨he,low,live,roots⟩ := first_coefficient (P.map ψ).roots (G.map ψ).eval
  have ham (i : ℕ) : (((determinant P G).coeff i).map φ).map ι =
      (product (P.map ψ).roots (G.map ψ).eval).coeff i := by
    rw [← hh,Polynomial.map_map]
    simp [mapTU,ψ]
  have card := (IsAlgClosed.splits (P.map ψ)).natDegree_eq_card_roots
  refine ⟨e,he.trans (card.symm.le.trans (hp.natDegree_map ψ).le),?_,?_,?_⟩
  · intro j hj
    exact (Polynomial.map_eq_zero_iff ι.injective).mp ((ham j).trans (low j hj))
  · intro h
    exact live ((ham e).symm.trans (by rw [h,Polynomial.map_zero]))
  · intro t
    have foo (F : ℚ[X]) : (F.map ι).IsRoot (ι t) ↔ F.IsRoot t := by
      change (F.map ι).eval (ι t) = 0 ↔ F.eval t = 0
      rw [eval_map_apply]
      exact map_eq_zero_iff ι ι.injective
    rw [← foo,ham,roots,mem_roots hpψ.ne_zero]
    have hp' : P.map ψ = (P.map φ).map ι := (Polynomial.map_map ..).symm
    have hg' : G.map ψ = (G.map φ).map ι := (Polynomial.map_map ..).symm
    rw [hp',foo,hg',eval_map_apply]
    simp [IsRoot.def]

end
end Sun28.Mask
#print axioms Sun28.Mask.determinant_product
#print axioms Sun28.Mask.specialize_product
#print axioms Sun28.Mask.rational_specialization
