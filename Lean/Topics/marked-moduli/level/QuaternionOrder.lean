import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The specified discriminant-six order, trace form and residue algebra at 3. -/
namespace ZInQBlueprint.LevelThree
open QuaternionAlgebra
abbrev F := ZMod 3
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)
abbrev O := QuaternionAlgebra ℤ (-1) 1 2
abbrev O₃ := QuaternionAlgebra F (-1) 1 2
abbrev A := QuaternionAlgebra F 2 0 0
abbrev K := QuadraticAlgebra F 2 0

instance : DecidableEq A := (QuaternionAlgebra.equivProd (2:F) 0 0).decidableEq
instance : Fintype A := Fintype.ofEquiv (F × F × F × F) (QuaternionAlgebra.equivProd (2:F) 0 0).symm

instance residueNonsquare : Fact (∀ r : F, r^2 ≠ 2+0*r) := ⟨by decide⟩

/-- Put ω=(1+j)/2. The four order coordinates are 1,ω,i,ωi. -/
def embed (x : O) : B :=
  ⟨x.re+x.imI/2, x.imJ+x.imK/2, x.imI/2, -x.imK/2⟩

theorem embed_mul (x y : O) : embed (x*y) = embed x * embed y := by
  ext <;> simp [embed] <;> push_cast <;> ring

theorem embed_injective : Function.Injective embed := by
  intro x y h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp [embed] at h0 h1 h2 h3
  rw [h2] at h0
  rw [h3] at h1
  exact QuaternionAlgebra.ext (by exact_mod_cast add_right_cancel h0) h2
    (by exact_mod_cast add_right_cancel h1) h3

/-- Coordinates in the order basis printed by V15: 1,i,ω,iω. -/
def printed {T : Type*} [CommRing T] (a b c d : T) : QuaternionAlgebra T (-1) 1 2 :=
  ⟨a,c,b+d,-d⟩

theorem span_printed (x : O) : ∃ a b c d, x = printed a b c d := by
  exact ⟨x.re,x.imJ+x.imK,x.imI,-x.imK, by ext <;> simp [printed]⟩

theorem embed_printed (a b c d : ℤ) :
    embed (printed a b c d) = (⟨a+c/2,b+d/2,c/2,d/2⟩ : B) := by
  ext <;> simp [embed, printed] <;> push_cast <;> ring

def mu : B := ⟨0,0,2,1⟩
def muInv : B := ⟨0,0,-1/3,-1/6⟩
def trd (z : B) : ℚ := 2*z.re
def tracePair (x y : B) : ℚ := trd (muInv*x*star y)

theorem mu_inverse : mu^2 = -6 ∧ mu*muInv = 1 ∧ muInv*mu = 1 := by
  constructor
  · ext <;> norm_num [mu,pow_two]
  constructor <;> ext <;> norm_num [mu, muInv]

/-- Divide by the different before reduction. -/
theorem trace_slots (x y : B) :
    tracePair x y = 2*((x*star y).imJ-(x*star y).imK) := by
  rw [tracePair, mul_assoc]
  simp [muInv,trd]
  ring

def gram {T : Type*} [CommRing T] (a b c d e f g h : T) : T :=
  a*(-g+h) + b*(g-2*h) + c*(e-f) + d*(-e+2*f)

theorem printed_trace (a b c d e f g h : ℤ) :
    tracePair (embed (printed a b c d)) (embed (printed e f g h)) =
        (gram a b c d e f g h : ℤ) := by
  rw [trace_slots, embed_printed, embed_printed]
  simp [gram]
  push_cast
  ring

/-- Reduction in the order basis, followed below by the change to 1,i,j,ij. -/
def reduceO (x : O) : O₃ := ⟨x.re,x.imI,x.imJ,x.imK⟩

theorem reduceO_mul (x y : O) : reduceO (x*y) = reduceO x * reduceO y := by
  ext <;> simp [reduceO] <;> push_cast <;> ring

theorem reduce_kernel (x : O) : reduceO x = 0 ↔
    (3:ℤ) ∣ x.re ∧ (3:ℤ) ∣ x.imI ∧ (3:ℤ) ∣ x.imJ ∧ (3:ℤ) ∣ x.imK := by
  rw [QuaternionAlgebra.ext_iff]
  change ((x.re:F) = 0 ∧ (x.imI:F) = 0 ∧ (x.imJ:F) = 0 ∧ (x.imK:F) = 0) ↔ _
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat]

def standard (x : O₃) : A :=
  ⟨x.re+2*x.imI,x.imJ+2*x.imK,2*x.imI,-2*x.imK⟩
def halfBasis (x : A) : O₃ := ⟨x.re-x.imJ,2*x.imJ,x.imI+x.imK,-2*x.imK⟩

local macro "mod_ring" : tactic =>
  `(tactic| (try ring_nf) <;> simp only [(show (3:F) = 0 by decide), (show (4:F) = 1 by decide), (show (5:F) = 2 by decide), (show (6:F) = 0 by decide), (show (7:F) = 1 by decide), (show (8:F) = 2 by decide), (show (9:F) = 0 by decide), (show (10:F) = 1 by decide), (show (11:F) = 2 by decide), (show (12:F) = 0 by decide), (show (13:F) = 1 by decide), (show (14:F) = 2 by decide), (show (15:F) = 0 by decide), (show (16:F) = 1 by decide), (show (17:F) = 2 by decide), (show (18:F) = 0 by decide), (show (19:F) = 1 by decide), (show (20:F) = 2 by decide), (show (21:F) = 0 by decide), (show (22:F) = 1 by decide), (show (23:F) = 2 by decide), (show (24:F) = 0 by decide), (show (25:F) = 1 by decide), (show (26:F) = 2 by decide), (show (27:F) = 0 by decide), (show (28:F) = 1 by decide), (show (29:F) = 2 by decide), mul_zero, mul_one, zero_mul, one_mul, zero_add, add_zero, sub_zero, neg_zero] <;> try ring)

def standardEquiv : O₃ ≃+* A where
  toFun := standard
  invFun := halfBasis
  left_inv x := by ext <;> simp [standard,halfBasis] <;> mod_ring
  right_inv x := by ext <;> simp [standard,halfBasis] <;> mod_ring
  map_mul' x y := by
    rcases x with ⟨a,b,c,d⟩
    rcases y with ⟨e,f,g,h⟩
    ext <;> simp [standard] <;> mod_ring <;> rw [show (2:F) = -1 by decide] <;> ring
  map_add' x y := by ext <;> simp [standard] <;> ring

def residual (x : A) : K := ⟨x.re,x.imI⟩
def radicalPart (x : A) : K := ⟨x.imJ,x.imK⟩
def assemble (a b : K) : A := ⟨a.re,a.im,b.re,b.im⟩
def nrd (x : A) : F := (residual x).norm

theorem field_card : Nat.card K = 9 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (2:F) 0), Nat.card_prod]
  simp [Nat.card_eq_fintype_card, F]

theorem frobenius (a : K) : a^3 = star a := by
  rcases a with ⟨x,y⟩
  revert x y
  decide

theorem skew_product (a b c d : K) :
    assemble a b * assemble c d = assemble (a*c) (a*d+b*c^3) := by
  rw [frobenius]
  ext <;> simp [assemble] <;> ring

theorem nrd_slots (x : A) : nrd x = x.re^2 - 2*x.imI^2 := by
  simp [nrd, residual, QuadraticAlgebra.norm_def]; ring

theorem nrd_neg (x : A) : nrd (-x) = nrd x := by simp [nrd_slots]

theorem nrd_mul (x y : A) : nrd (x*y) = nrd x * nrd y := by
  simp [nrd_slots]; ring

theorem nrd_star (x : A) : x * star x = (algebraMap F A) (nrd x) ∧ star x * x = (algebraMap F A) (nrd x) := by
  constructor <;> ext <;> simp [nrd_slots,QuaternionAlgebra.algebraMap_eq] <;> ring

theorem unit_iff (x : A) : IsUnit x ↔ nrd x ≠ 0 := by
  constructor
  · rintro ⟨u,rfl⟩ h
    have hu : nrd ((u:A)*(↑u⁻¹:A)) = 1 := by simp [nrd_slots]
    rw [nrd_mul,h,zero_mul] at hu
    exact zero_ne_one hu
  · intro h
    let c := (algebraMap F A) (nrd x)⁻¹
    have ce : Commute c x := Algebra.commutes _ _
    have h1 : (algebraMap F A) (nrd x) * c = 1 := by
      calc
        _ = (algebraMap F A) (nrd x * (nrd x)⁻¹) := (map_mul _ _ _).symm
        _ = 1 := by rw [mul_inv_cancel₀ h, map_one]
    refine ⟨⟨x,star x*c,?_,?_⟩,rfl⟩
    · rw [← mul_assoc,(nrd_star x).1,h1]
    · rw [mul_assoc,ce.eq,← mul_assoc,(nrd_star x).2,h1]

def pairing (x y : A) : F := 2*((x*star y).imJ-(x*star y).imK)

theorem reduced_printed_pairing (a b c d e f g h : F) :
    pairing (standard (printed a b c d)) (standard (printed e f g h)) = gram a b c d e f g h := by
  simp [pairing,standard,printed,gram]
  mod_ring

theorem pairing_change (x y t : A) :
    pairing (x*t) (y*t) = nrd t * pairing x y := by
  simp [pairing,nrd_slots]
  ring

theorem pairing_alternating (x : A) : pairing x x = 0 := by
  rw [pairing, (nrd_star x).1]
  simp [QuaternionAlgebra.algebraMap_eq]

theorem pairing_nondegenerate (x : A) (h : ∀ y, pairing x y = 0) : x = 0 := by
  have h0 := h ⟨1,0,0,0⟩
  have h1 := h ⟨0,1,0,0⟩
  have h2 := h ⟨0,0,1,0⟩
  have h3 := h ⟨0,0,0,1⟩
  simp [pairing] at h0 h1 h2 h3
  clear h
  rcases x with ⟨a,b,c,d⟩
  revert h0 h1 h2 h3
  revert a b c d
  decide

#print axioms embed_mul
#print axioms embed_injective
#print axioms span_printed
#print axioms mu_inverse
#print axioms printed_trace
#print axioms reduce_kernel
#print axioms standardEquiv
#print axioms field_card
#print axioms frobenius
#print axioms skew_product
#print axioms nrd_slots
#print axioms unit_iff
#print axioms reduced_printed_pairing
#print axioms pairing_change
#print axioms pairing_alternating
#print axioms pairing_nondegenerate

end ZInQBlueprint.LevelThree
