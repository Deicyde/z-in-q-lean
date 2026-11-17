import ZInQKernel.RouteK.RankVariants

/-! Integer factorizations in the second coefficient of Tian--Yuan--Zhang,
Asian J. Math. 21 (2017), proof of Theorem 3.5(2), p. 760. -/

open Finset
open ZInQ.RouteK.Rank5b
open scoped BigOperators

namespace ZInQBlueprint.TYZ

abbrev PrimePartition (d : ℕ) := Finpartition (univ : Finset d.primeFactors)

/-- All unordered factorizations into integers greater than one.  The empty
factorization is admitted precisely for the integer one. -/
def factorizations (d : ℕ) : Finset (Finset ℕ) :=
  d.divisors.powerset.filter fun F => (∀ a ∈ F, 1 < a) ∧ ∏ a ∈ F, a = d

theorem mem_factorizations {d : ℕ} (hd : d ≠ 0) (F : Finset ℕ) :
    F ∈ factorizations d ↔ (∀ a ∈ F, 1 < a) ∧ ∏ a ∈ F, a = d := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · rintro ⟨hlt, hprod⟩
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hlt, hprod⟩
    intro a ha
    exact Nat.mem_divisors.mpr ⟨hprod ▸ dvd_prod_of_mem id ha, hd⟩

/-- Prime divisors of a prospective integer factor, as primes of the ambient integer. -/
def primeBlock (d a : ℕ) : Finset d.primeFactors := univ.filter fun p => (p : ℕ) ∣ a

@[simp] theorem mem_primeBlock {d a : ℕ} {p : d.primeFactors} :
    p ∈ primeBlock d a ↔ (p : ℕ) ∣ a := by simp [primeBlock]

theorem primeBlock_dProd {d : ℕ} (B : Finset d.primeFactors) :
    primeBlock d (dProd B) = B := by
  ext p
  rw [mem_primeBlock, dProd, (Nat.prime_of_mem_primeFactors p.property).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hdvd⟩
    have hpq := ((Nat.dvd_prime (Nat.prime_of_mem_primeFactors q.property)).mp hdvd).resolve_left
      (Nat.prime_of_mem_primeFactors p.property).ne_one
    exact (Subtype.ext hpq : p = q) ▸ hq
  · intro hp
    exact ⟨p, hp, dvd_rfl⟩

theorem dProd_primeBlock {d a : ℕ} (hs : Squarefree d) (ha : a ∣ d) :
    dProd (primeBlock d a) = a := by
  have hsa := Squarefree.squarefree_of_dvd ha hs
  let val : d.primeFactors ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (primeBlock d a).map val = a.primeFactors := by
    ext p
    constructor
    · intro h
      obtain ⟨q, hq, rfl⟩ := mem_map.mp h
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors q.property,
        mem_primeBlock.mp hq, hsa.ne_zero⟩
    · intro hp
      obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
      let q : d.primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hprime, hdiv.trans ha, hs.ne_zero⟩⟩
      exact mem_map.mpr ⟨q, mem_primeBlock.mpr hdiv, rfl⟩
  calc
    dProd (primeBlock d a) = ∏ p ∈ (primeBlock d a).map val, p :=
      (Finset.prod_map _ val id).symm
    _ = a := hmap ▸ Nat.prod_primeFactors_of_squarefree hsa

def blockProduct (d : ℕ) : Finset d.primeFactors ↪ ℕ where
  toFun := dProd
  inj' := by
    intro B C h
    simpa only [primeBlock_dProd] using congrArg (primeBlock d) h

def factors {d : ℕ} (P : PrimePartition d) : Finset ℕ := P.parts.map (blockProduct d)

theorem factors_injective {d : ℕ} : Function.Injective (@factors d) :=
  fun _ _ h => Finpartition.ext (Finset.map_injective _ h)

theorem product_factors {d : ℕ} (hs : Squarefree d) (P : PrimePartition d) :
    ∏ a ∈ factors P, a = d := by
  rw [factors, Finset.prod_map]
  change (∏ B ∈ P.parts, ∏ p ∈ B, (p : ℕ)) = d
  have h := Finset.prod_biUnion (f := fun p : d.primeFactors => (p : ℕ)) P.disjoint
  rw [P.biUnion_parts] at h
  simp only [id_eq] at h
  rw [← h, Finset.prod_coe_sort_eq_attach, Finset.prod_attach d.primeFactors (fun q => q)]
  exact Nat.prod_primeFactors_of_squarefree hs

theorem factors_mem {d : ℕ} (hs : Squarefree d) (P : PrimePartition d) :
    factors P ∈ factorizations d := by
  refine (mem_factorizations hs.ne_zero _).mpr ⟨?_, product_factors hs P⟩
  intro a ha
  obtain ⟨B, hB, rfl⟩ := mem_map.mp ha
  obtain ⟨p, hp⟩ := P.nonempty_of_mem_parts hB
  exact (Nat.prime_of_mem_primeFactors p.property).one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (dProd B))) (dvd_prod_of_mem (fun q : d.primeFactors => (q : ℕ)) hp))

private theorem unique_owner {d p a b : ℕ} {F : Finset ℕ} (hs : Squarefree d)
    (hp : p.Prime) (hprod : ∏ t ∈ F, t = d)
    (ha : a ∈ F) (hb : b ∈ F) (hpa : p ∣ a) (hpb : p ∣ b) : a = b := by
  by_contra hab
  have hsub : ({a,b} : Finset ℕ) ⊆ F := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb
  have habd := Finset.prod_dvd_prod_of_subset _ _ id hsub
  rw [Finset.prod_pair hab] at habd
  exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp)
    ((Nat.mul_dvd_mul hpa hpb).trans (hprod ▸ habd))

/-- Inverse construction by unique prime divisibility in a squarefree product. -/
def partitionOf {d : ℕ} (hs : Squarefree d) (F : Finset ℕ) (hF : F ∈ factorizations d) :
    PrimePartition d := by
  classical
  obtain ⟨hlt, hprod⟩ := (mem_factorizations hs.ne_zero F).mp hF
  refine Finpartition.ofExistsUnique (F.image (primeBlock d)) (fun _ _ => subset_univ _) ?_ ?_
  · intro p _
    have hpr := (Nat.prime_of_mem_primeFactors p.property).prime
    have hdiv := (Nat.dvd_of_mem_primeFactors p.property).trans (dvd_of_eq hprod.symm)
    obtain ⟨a, ha, hpa⟩ := (hpr.dvd_finsetProd_iff id).mp hdiv
    refine ⟨primeBlock d a, ⟨mem_image_of_mem _ ha, mem_primeBlock.mpr hpa⟩, ?_⟩
    rintro B ⟨hB, hpB⟩
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hB
    exact congrArg (primeBlock d) (unique_owner hs (Nat.prime_of_mem_primeFactors p.property)
      hprod hb ha (mem_primeBlock.mp hpB) hpa)
  · intro hemp
    obtain ⟨a, ha, h⟩ := mem_image.mp hemp
    have had : a ∣ d := hprod ▸ dvd_prod_of_mem id ha
    have hone : a = 1 := by
      rw [← dProd_primeBlock hs had, h]
      simp [dProd]
    exact (ne_of_gt (hlt a ha)) hone

theorem parts_partitionOf {d : ℕ} (hs : Squarefree d) {F : Finset ℕ} (hF : F ∈ factorizations d) :
    (partitionOf hs F hF).parts = F.image (primeBlock d) := rfl

theorem factors_partitionOf {d : ℕ} (hs : Squarefree d) {F : Finset ℕ} (hF : F ∈ factorizations d) :
    factors (partitionOf hs F hF) = F := by
  have hprod := ((mem_factorizations hs.ne_zero F).mp hF).2
  have had (a : ℕ) (ha : a ∈ F) : a ∣ d := hprod ▸ dvd_prod_of_mem id ha
  ext a
  rw [factors, parts_partitionOf, mem_map]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hB
    change dProd (primeBlock d b) ∈ F
    rwa [dProd_primeBlock hs (had b hb)]
  · intro ha
    exact ⟨primeBlock d a, mem_image_of_mem _ ha, dProd_primeBlock hs (had a ha)⟩

/-- All unordered prime partitions correspond exactly to all unordered integer
factorizations of a squarefree natural number, before restricting residues. -/
def factorizationEquiv (d : ℕ) (hs : Squarefree d) : PrimePartition d ≃ ↥(factorizations d) where
  toFun P := ⟨factors P, factors_mem hs P⟩
  invFun F := partitionOf hs F.val F.property
  left_inv P := factors_injective (factors_partitionOf hs (factors_mem hs P))
  right_inv F := Subtype.ext (factors_partitionOf hs F.property)

#print axioms factorizationEquiv

end ZInQBlueprint.TYZ
