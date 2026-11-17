import CoefficientSeparator
import ResultantGuards

/-! Detect separating projections of a specialized monic tower by polynomial
coefficient tests over the original parameter ring. -/
open Polynomial Finset ZInQBlueprint.SunTower ZInQBlueprint.SunResultant
open ZInQBlueprint.SunResultant.ParamTower
namespace Sun28.Compiler
noncomputable section
variable {R L : Type*} [CommRing R] [Field L] {n : ℕ}

/-- The determinant has two fixed row-block sizes, chosen before specialization. -/
def fixedCollision (P : R[X]) (D : ℕ) : R[X] :=
  let q := P.map (C : R →+* R[X])
  resultant q (q.comp (X + C X)) D D

theorem fixedCollision_map (P : R[X]) (D : ℕ) (φ : R →+* L)
    (hd : (P.map φ).natDegree = D) :
    (fixedCollision P D).map φ = Collision.shiftedResultant (P.map φ) := by
  let ρ := Polynomial.mapRingHom φ
  let q := P.map (C : R →+* R[X])
  let q' := (P.map φ).map (C : L →+* L[X])
  have hq : q.map ρ = q' := by
    simp only [q,q',Polynomial.map_map]
    congr 1
    ext r
    simp [ρ]
  have hs : (q.comp (X + C X)).map ρ = q'.comp (X+C X) := by
    rw [Polynomial.map_comp,hq]
    simp [ρ]
  have deg : q'.natDegree = D := by
    rw [show q'=(P.map φ).map (C : L →+* L[X]) from rfl,natDegree_map_eq_of_injective C_injective]
    exact hd
  have deg' : (q'.comp (X+C X)).natDegree = D := by
    rw [natDegree_comp,natDegree_X_add_C,mul_one,deg]
  change ρ (resultant q (q.comp (X+C X)) D D) =
    resultant q' (q'.comp (X+C X)) q'.natDegree (q'.comp (X+C X)).natDegree
  rw [←resultant_map_map,hq,hs,deg,deg']

def bound (T : ParamTower R n) : ℕ := T.degreeProduct.choose 2 * (n-1)

def collision (T : ParamTower R n) (b : ℕ) : R[X] :=
  fixedCollision (imagePolynomial T (linearForm R n b)) T.degreeProduct

/-- This condition consists exclusively of parameter equalities and one inequation. -/
def Selected (T : ParamTower R n) (φ : R →+* L) (b d : ℕ) : Prop :=
  φ ((collision T b).coeff d) ≠ 0 ∧ ∀ j ≤ bound T, ∀ k < d, φ ((collision T j).coeff k) = 0

theorem collision_map [IsAlgClosed L] [CharZero L] [DecidableEq L]
    (T : ParamTower R n) (φ : R →+* L) (b : ℕ) :
    (collision T b).map φ = Collision.shiftedResultant
      (Collision.projected (rootTuples φ T).toFinset (separator (b:L)) (rootTuples φ T).count) := by
  rw [collision,fixedCollision_map _ _ _ (imagePolynomial_degree T _ φ),imagePolynomial_map,
    Finset.prod_multiset_map_count]
  simp [Collision.projected,linearForm,separator]

theorem fibre_card_bound [IsAlgClosed L] [DecidableEq L] (T : ParamTower R n) (φ : R →+* L) :
    (rootTuples φ T).toFinset.card.choose 2 * (n-1) ≤ bound T := by
  exact Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 ((Multiset.toFinset_card_le _).trans_eq (card_rootTuples φ T)))

theorem selects_iff [IsAlgClosed L] [CharZero L] [DecidableEq L]
    (T : ParamTower R n) (φ : R →+* L) (b : ℕ) :
    Set.InjOn (separator (b:L)) ((rootTuples φ T).toFinset : Set (Fin n → L)) ↔
      ∃ d ≤ T.degreeProduct^2, Selected T φ b d := by
  let M := rootTuples φ T
  have pos (x) (h : x ∈ M.toFinset) : 0 < M.count x :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp h)
  have h := Collision.separates_iff_coefficient_branch M.toFinset M.count pos (b:=b) (fibre_card_bound T φ)
  simp only [M,Multiset.toFinset_sum_count_eq,card_rootTuples,Collision.CoefficientMinimum,
    ←collision_map,coeff_map] at h
  exact h

#print axioms fixedCollision_map
#print axioms collision_map
#print axioms selects_iff
end
end Sun28.Compiler
