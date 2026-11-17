import ClusterPicture
import Mathlib

/-! Move a finite branch point of a split sextic to infinity, retaining its twist. -/
namespace SixContactFour
open Finset
noncomputable section
variable {R : Type*} [CommRing R]

/-- The coefficient of the odd-degree radicand after inverting about the sixth branch. -/
def branchScale (c b : R) (r : Fin 5 → R) : R := c*∏ i, (b-r i)

/-- The five finite roots after the scale that makes the quintic monic. -/
def oddRoot (c b : R) (r : Fin 5 → R) (i : Fin 5) : R :=
  -c*∏ k ∈ univ.erase i, (b-r k)

theorem branchScale_eq (c b : R) (r : Fin 5 → R) (i : Fin 5) :
    branchScale c b r = -(b-r i)*oddRoot c b r i := by
  have h := (univ : Finset (Fin 5)).mul_prod_erase (fun k => b-r k) (mem_univ i)
  unfold branchScale oddRoot
  rw [←h]
  ring

/-- Every transformed branch difference is a product of one original difference
and the three differences from the distinguished root complementary to the pair. -/
theorem oddRoot_sub (c b : R) (r : Fin 5 → R) (i j : Fin 5) (hij : i ≠ j) :
    oddRoot c b r i-oddRoot c b r j =
      -c*(r i-r j)*∏ k ∈ (univ.erase i).erase j, (b-r k) := by
  have h1 := (univ.erase i).mul_prod_erase (fun k : Fin 5 => b-r k)
    (show j ∈ univ.erase i by simp [Ne.symm hij])
  have h2 := (univ.erase j).mul_prod_erase (fun k : Fin 5 => b-r k)
    (show i ∈ univ.erase j by simp [hij])
  have erase : ((univ : Finset (Fin 5)).erase j).erase i=(univ.erase i).erase j := by
    ext k; simp [and_comm]
  rw [erase] at h2
  unfold oddRoot
  rw [←h1,←h2]
  ring

variable {K : Type*} [Field K]

theorem monic_product (c b : K) (r : Fin 5 → K) (hb : ∀ i, b ≠ r i) :
    ∏ i, (-oddRoot c b r i) = c*(branchScale c b r)^4 := by
  let D := branchScale c b r
  have inv (i : Fin 5) : -oddRoot c b r i=D/(b-r i) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hb i))).mpr
    dsimp only [D]
    conv_rhs => rw [branchScale_eq c b r i]
    ring
  simp_rw [inv]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  dsimp only [D,branchScale]
  have hprod : (∏ i : Fin 5, (b-r i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hb i))
  field_simp [hprod]

/-- On x≠b the original signed equation pulls back to the actual monic quintic. -/
theorem monic_quintic (c b : K) (r : Fin 5 → K) {x y : K}
    (hx : x ≠ b) (hb : ∀ i, b ≠ r i)
    (he : y^2=c*(x-b)*∏ i, (x-r i)) :
    (y/(x-b)^3*(branchScale c b r)^2)^2 =
      ∏ i, (branchScale c b r/(x-b)-oddRoot c b r i) := by
  let D := branchScale c b r
  have x0 : x-b ≠ 0 := sub_ne_zero.mpr hx
  have term (i : Fin 5) :
      branchScale c b r/(x-b)-oddRoot c b r i =
        (-oddRoot c b r i)*(x-r i)/(x-b) := by
    rw [branchScale_eq c b r i]
    field_simp
    ring
  have Dprod := monic_product c b r hb
  simp_rw [term]
  rw [prod_div_distrib,prod_mul_distrib,Dprod]
  simp only [prod_const,card_univ,Fintype.card_fin]
  change (y/(x-b)^3*D^2)^2=_
  rw [mul_pow,div_pow,he]
  field_simp [x0]
  rfl

end
end SixContactFour
#print axioms SixContactFour.branchScale_eq
#print axioms SixContactFour.oddRoot_sub
#print axioms SixContactFour.monic_product
#print axioms SixContactFour.monic_quintic
