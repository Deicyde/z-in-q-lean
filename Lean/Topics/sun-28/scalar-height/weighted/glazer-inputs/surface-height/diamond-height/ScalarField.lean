import DiamondTransfer
import PairedEuler
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- Count a finite-image character by embedding its image into the roots of unity. -/
theorem character_index {G K : Type*} [Group G] [Field K] (χ : G →* Kˣ)
    {n : ℕ} (hn : 0<n) (ann : ∀ g, (χ g)^n=1) : χ.ker.index ≤ n := by
  let : NeZero n := ⟨hn.ne'⟩
  have sub : χ.range ≤ rootsOfUnity n K := by
    rintro a ⟨g,rfl⟩
    exact (mem_rootsOfUnity ..).mpr (ann g)
  rw [Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective sub)).trans
    (card_rootsOfUnity K n)

/-- The same exponent annihilates every product of odd local residue characters.
The character modulo four contributes the initial factor two. -/
theorem local_character_product {G K : Type*} [Group G] [CommGroup K]
    (R : ℕ) (δ : G →* K) (dyadic : ∀ g, (δ g)^2=1)
    (ι : ∀ p : ℕ, G →* (ZMod p)ˣ) (χ : ∀ p : ℕ, (ZMod p)ˣ →* K) (g : G) :
    (δ g * ∏ p ∈ R.primeFactors, χ p (ι p g)) ^ (2*unitOrders R) = 1 := by
  rw [mul_pow, pow_mul, dyadic, one_pow, one_mul, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro p hp
  have prime:=Nat.prime_of_mem_primeFactors hp
  let : NeZero p := ⟨prime.ne_zero⟩
  have order : (ι p g)^(p-1)=1 := by
    rw [← Nat.totient_prime prime, ← ZMod.card_units_eq_totient]
    exact pow_card_eq_one
  have divides : p-1 ∣ 2*unitOrders R := dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun p:ℕ => p-1) hp) _
  obtain ⟨v,e⟩:=divides
  rw [e,pow_mul,←map_pow,order,map_one,one_pow]

/-- The field on which the cochain restricts to one and its determinant character. -/
structure ScalarTower (R : ℕ) where
  marking : Subgroup (Field.absoluteGaloisGroup ℚ)
  marking_pos : 0<marking.index
  marking_degree : marking.index≤576
  m : ℕ
  m_pos : 0<m
  order_bound : m≤2*unitOrders R
  scalar : marking →* ℂˣ
  exponent_bound : ∀ g, (scalar g)^(2*m)=1
  normal : (scalar.ker.map marking.subtype).Normal
  determinant : Field.absoluteGaloisGroup ℚ →* ℂˣ
  square : ∀ g ∈ scalar.ker.map marking.subtype, (determinant g)^2=1

def ScalarTower.fieldDegree {R:ℕ} (S : ScalarTower R) := (S.scalar.ker.map S.marking.subtype).index

theorem scalar_field_degree {R:ℕ} (S : ScalarTower R) : S.fieldDegree≤2304*unitOrders R := by
  rw [ScalarTower.fieldDegree,Subgroup.index_map_subtype]
  have a:=character_index S.scalar (Nat.mul_pos (by decide) S.m_pos) S.exponent_bound
  calc
    _ ≤ (2*(2*unitOrders R))*576 := Nat.mul_le_mul (a.trans (Nat.mul_le_mul_left _ S.order_bound)) S.marking_degree
    _ = _ := by ring

theorem field_degree_pos {R:ℕ} (S : ScalarTower R) : 0<S.fieldDegree := by
  rw [ScalarTower.fieldDegree,Subgroup.index_map_subtype]
  have bound : Finite S.scalar.range := by
    have sub : S.scalar.range ≤ rootsOfUnity (2*S.m) ℂ := by
      rintro a ⟨g,rfl⟩;exact (mem_rootsOfUnity ..).mpr (S.exponent_bound g)
    let : NeZero (2*S.m) := ⟨(Nat.mul_pos (by decide) S.m_pos).ne'⟩
    exact Finite.of_injective _ (Subgroup.inclusion_injective sub)
  rw [Subgroup.index_ker]
  exact Nat.mul_pos Nat.card_pos S.marking_pos

theorem determinant_index {R:ℕ} (S : ScalarTower R) :
    S.determinant.ker.index ≤ 2*S.fieldDegree := by
  let _ := S.normal
  apply character_index S.determinant (Nat.mul_pos (by decide) (field_degree_pos S))
  intro g
  rw [Nat.mul_comm,pow_mul,←map_pow]
  exact S.square _ ((S.scalar.ker.map S.marking.subtype).pow_index_mem g)

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.character_index
#print axioms ZInQBlueprint.DiamondHeight.local_character_product
#print axioms ZInQBlueprint.DiamondHeight.scalar_field_degree
#print axioms ZInQBlueprint.DiamondHeight.field_degree_pos
#print axioms ZInQBlueprint.DiamondHeight.determinant_index
