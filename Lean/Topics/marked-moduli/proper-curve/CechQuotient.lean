import FiniteDoubleCover
import Mathlib.LinearAlgebra.Isomorphisms

/-! The first Čech quotient for the two affine charts of a binary sextic. -/
open CategoryTheory AlgebraicGeometry Polynomial LaurentPolynomial
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
variable (k : Type) [Field k]
local notation "L" => LaurentPolynomial k
attribute [local instance] QuadraticAlgebra.algebra

/-- Restrict a function on the finite chart to the common punctured chart. -/
def direct (f : k[X]) : Cover f →ₐ[k] Punctured k f :=
  { (algebraMap (Cover f) (Punctured k f)) with
    commutes' := fun r => QuadraticAlgebra.ext (Polynomial.toLaurent_C r) (map_zero _) }

/-- Restrict a function on the infinity chart using the model's actual transition. -/
def reciprocal {f g : k[X]} (h : SexticOverlap k f g) : Cover g →ₐ[k] Punctured k f :=
  (transition k h).symm.toAlgHom.comp (direct k g)

theorem direct_spec (f g : k[X]) (h : SexticOverlap k f g) :
    Spec.map (CommRingCat.ofHom (direct k f).toRingHom) = arrow k f g h false := rfl

theorem reciprocal_spec (f g : k[X]) (h : SexticOverlap k f g) :
    Spec.map (CommRingCat.ofHom (reciprocal k h).toRingHom) = arrow k f g h true := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

private theorem unit_inverse : (↑(laurentUnit k (-3))⁻¹ : L) = T 3 := by
  apply (laurentUnit k (-3)).inv_eq_of_mul_eq_one_right
  change (T (-3) : L) * T 3 = 1
  rw [← T_add]; norm_num

theorem direct_coords {f : k[X]} (p q : k[X]) :
    direct k f ⟨p,q⟩ = ⟨p.toLaurent,q.toLaurent⟩ := rfl

theorem reciprocal_coords {f g : k[X]} (h : SexticOverlap k f g) (p q : k[X]) :
    reciprocal k h ⟨p,q⟩ = ⟨invert p.toLaurent, T (-3) * invert q.toLaurent⟩ := by
  apply QuadraticAlgebra.ext
  · rfl
  · change invert.symm ((↑(laurentUnit k (-3))⁻¹ : L) * q.toLaurent) = _
    rw [unit_inverse, invert_symm, map_mul, invert_T]

/-- The difference of restrictions on the two-term alternating Čech complex. -/
def differential {f g : k[X]} (h : SexticOverlap k f g) :
    Cover f × Cover g →ₗ[k] Punctured k f :=
  (direct k f).toLinearMap.comp (LinearMap.fst k _ _) -
    (reciprocal k h).toLinearMap.comp (LinearMap.snd k _ _)

/-- The only Laurent coefficients outside the images of the two odd summands. -/
def residues (f : k[X]) : Punctured k f →ₗ[k] k × k where
  toFun z := (z.im.coeff (-1), z.im.coeff (-2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mon (a : k) (i : ℤ) : L := LaurentPolynomial.C a * T i

private theorem coeff_mon (a : k) (i j : ℤ) :
    (mon k a i).coeff j = if i=j then a else 0 := by
  rw [mon, ← single_eq_C_mul_T]
  exact Finsupp.single_apply

private theorem image_monomial (a : k) (n : ℕ) :
    (Polynomial.monomial n a).toLaurent = mon k a n :=
  Polynomial.toLaurent_C_mul_T n a

private theorem opposite_monomial (a : k) (n : ℕ) (d : ℤ) :
    T d * invert (Polynomial.toLaurent (Polynomial.monomial n a)) = mon k a (d - n) := by
  rw [image_monomial, mon, map_mul, invert_C, invert_T, mon, T_sub]
  ring

private theorem direct_coeff (p : k[X]) (i : ℤ) (hi : i<0) : p.toLaurent.coeff i = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    change p.toLaurent.coeff i + q.toLaurent.coeff i = 0
    rw [hp,hq,add_zero]
  | monomial n a =>
    rw [image_monomial,coeff_mon,ite_eq_right (by omega)]

private theorem opposite_coeff (p : k[X]) (i : ℤ) (hi : (-3 : ℤ) < i) :
    ((T (-3) : L) * invert p.toLaurent).coeff i = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add,map_add,mul_add]
    change ((T (-3) : L)*invert p.toLaurent).coeff i + ((T (-3) : L)*invert q.toLaurent).coeff i = 0
    rw [hp,hq,add_zero]
  | monomial n a =>
    rw [opposite_monomial,coeff_mon,ite_eq_right (by omega)]

private theorem even_decompose (z : L) :
    ∃ a c : k[X], z = a.toLaurent - invert c.toLaurent := by
  induction z using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,c,ha⟩ := hp
    obtain ⟨b,d,hb⟩ := hq
    exact ⟨a+b,c+d, by rw [ha,hb,map_add,map_add,map_add]; abel⟩
  | C_mul_T i a =>
    by_cases hi : 0 ≤ i
    · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
      exact ⟨Polynomial.monomial n a,0,by simp⟩
    · have e : i = - ((-i).toNat : ℤ) := by omega
      refine ⟨0,-Polynomial.monomial (-i).toNat a,?_⟩
      rw [map_zero,map_neg,map_neg,sub_neg_eq_add,zero_add,image_monomial,mon,map_mul,invert_C,invert_T]
      rw [← e]

private def representative (f : k[X]) (a b : k) : Punctured k f :=
  ⟨0, mon k a (-1) + mon k b (-2)⟩

private theorem residues_surjective (f : k[X]) : Function.Surjective (residues k f) := by
  rintro ⟨a,b⟩
  refine ⟨representative k f a b,?_⟩
  change ((mon k a (-1)).coeff (-1) + (mon k b (-2)).coeff (-1),
    (mon k a (-1)).coeff (-2) + (mon k b (-2)).coeff (-2)) = _
  simp [coeff_mon]

private theorem odd_decompose (z : L) :
    ∃ a c : k[X], z = a.toLaurent - T (-3) * invert c.toLaurent +
      (mon k (z.coeff (-1)) (-1) + mon k (z.coeff (-2)) (-2)) := by
  induction z using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,c,ha⟩ := hp
    obtain ⟨b,d,hb⟩ := hq
    refine ⟨a+b,c+d,?_⟩
    change p+q = _ + (mon k (p.coeff (-1)+q.coeff (-1)) (-1) + mon k (p.coeff (-2)+q.coeff (-2)) (-2))
    simp only [map_add,mul_add,mon,add_mul] at *
    linear_combination ha + hb
  | C_mul_T i r =>
    change ∃ a c : k[X], mon k r i = a.toLaurent - T (-3) * invert c.toLaurent +
      (mon k ((mon k r i).coeff (-1)) (-1) + mon k ((mon k r i).coeff (-2)) (-2))
    simp only [coeff_mon]
    by_cases hi : 0 ≤ i
    · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
      refine ⟨Polynomial.monomial n r,0,?_⟩
      simp [mon,show (n:ℤ)≠ -1 by omega,show (n:ℤ)≠ -2 by omega]
    · by_cases small : i ≤ -3
      · have e : (-3 : ℤ) - ((-3-i).toNat : ℤ) = i := by omega
        refine ⟨0,-Polynomial.monomial (-3-i).toNat r,?_⟩
        rw [map_zero,map_neg,map_neg,mul_neg,sub_neg_eq_add,zero_add,opposite_monomial,e]
        simp [show i≠ -1 by omega,show i≠ -2 by omega,mon]
      · have e : i = -1 ∨ i = -2 := by omega
        rcases e with rfl | rfl <;> exact ⟨0,0,by simp [mon]⟩

theorem range_eq_ker {f g : k[X]} (h : SexticOverlap k f g) :
    LinearMap.range (differential k h) = LinearMap.ker (residues k f) := by
  ext z
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,rfl⟩
    change residues k f (direct k f ⟨a,b⟩ - reciprocal k h ⟨c,d⟩) = 0
    rw [direct_coords,reciprocal_coords]
    apply Prod.ext
    · change b.toLaurent.coeff (-1) - ((T (-3) : L)*invert d.toLaurent).coeff (-1) = 0
      rw [direct_coeff k _ _ (by decide),opposite_coeff k _ _ (by decide),sub_zero]
    · change b.toLaurent.coeff (-2) - ((T (-3) : L)*invert d.toLaurent).coeff (-2) = 0
      rw [direct_coeff k _ _ (by decide),opposite_coeff k _ _ (by decide),sub_zero]
  · intro hz
    change (z.im.coeff (-1),z.im.coeff (-2)) = (0,0) at hz
    have h₁ : z.im.coeff (-1) = 0 := congrArg Prod.fst hz
    have h₂ : z.im.coeff (-2) = 0 := congrArg Prod.snd hz
    obtain ⟨a,c,hac⟩ := even_decompose k z.re
    obtain ⟨b,d,hbd⟩ := odd_decompose k z.im
    simp only [h₁,h₂,mon,map_zero,zero_mul,add_zero] at hbd
    refine ⟨(⟨a,b⟩,⟨c,d⟩),?_⟩
    change direct k f ⟨a,b⟩ - reciprocal k h ⟨c,d⟩ = z
    rw [direct_coords,reciprocal_coords]
    exact QuadraticAlgebra.ext hac.symm hbd.symm

/-- First alternating Čech cohomology of the two displayed affine charts,
as the cokernel of their actual restriction difference. -/
def quotientEquiv {f g : k[X]} (h : SexticOverlap k f g) :
    (Punctured k f ⧸ LinearMap.range (differential k h)) ≃ₗ[k] k × k :=
  (Submodule.quotEquivOfEq _ _ (range_eq_ker k h)).trans
    ((residues k f).quotKerEquivOfSurjective (residues_surjective k f))

theorem quotient_coordinates {f g : k[X]} (h : SexticOverlap k f g) (z : Punctured k f) :
    quotientEquiv k h (Submodule.Quotient.mk z) = (z.im.coeff (-1), z.im.coeff (-2)) := rfl

theorem quotient_finrank {f g : k[X]} (h : SexticOverlap k f g) :
    Module.finrank k (Punctured k f ⧸ LinearMap.range (differential k h)) = 2 := by
  rw [(quotientEquiv k h).finrank_eq]
  simp

theorem paper_quotient_finrank [CharZero k] (u : ℚ) :
    Module.finrank k (Punctured k (paper k u false) ⧸
      LinearMap.range (differential k (paper_overlap k u))) = 2 :=
  quotient_finrank k _

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.direct_spec
#print axioms ZInQBlueprint.BinaryCover.Cech.reciprocal_spec
#print axioms ZInQBlueprint.BinaryCover.Cech.quotient_coordinates
#print axioms ZInQBlueprint.BinaryCover.Cech.quotientEquiv
#print axioms ZInQBlueprint.BinaryCover.Cech.paper_quotient_finrank
