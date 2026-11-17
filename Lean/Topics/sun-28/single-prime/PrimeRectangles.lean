import PrimeFibre
import BoxRecords
import LocalFractions

namespace Sun28.SinglePrime
open Finset Sun28.WeightedSelection Sun28.MixedSieve Sun28.ContactFactors
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

def mass (S : Finset (Record A d H Y)) (P : Record A d H Y→Prop) : ℝ :=
  ∑ a∈S,if P a then weight a else 0

def clear (a : Record A d H Y) (p : ℕ) (e : Bool) : Prop :=
  ∀ i,¬p∣adjacentNorm (a.gaussian i) e

def passes (a : Record A d H Y) (p : ℕ) (j : Test) : Prop :=
  accepts (clear a p true) (clear a p false) j

theorem rectangle_test (a : Record A d H Y) (p : ℕ) [Fact p.Prime] (j : Test) :
    primeFibre a p ∈ rectangle j _ ↔ passes a p j := by
  cases j <;>
    simp only [passes,rectangle,accepts,safeBox,clear,Finset.mem_inter,Fintype.mem_piFinset,
      Finset.mem_compl,fibre_bad_iff]

theorem prime_test (a : Record A d H Y) (T : Finset ℕ) (κ p : ℕ) [Fact p.Prime]
    (odd : p≠2) (outside : p∉T) (aux : p∉κ.primeFactors) :
    atPrime a.gaussian T κ p ↔ clear a p true ∨ clear a p false := by
  rw [atPrime_iff_fibre a T κ p odd outside aux,good_iff_union,Finset.mem_union]
  exact or_congr (rectangle_test a p .plus) (rectangle_test a p .minus)

def baseSet (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K : ℕ) : Finset (Record A d H Y) :=
  S.filter fun a => below a T κ K

def baseCount (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K : ℕ) : ℝ :=
  ∑ a∈baseSet S T κ K,weight a

def rectCount (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K p : ℕ) (j : Test) : ℝ :=
  mass (baseSet S T κ K) fun a=>passes a p j

def badCount (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K p : ℕ) : ℝ :=
  mass (baseSet S T κ K) fun a=>¬atPrime a.gaussian T κ p

theorem bad_count (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K p : ℕ)
    (prime : p.Prime) (odd : p≠2) (outside : p∉T) (aux : p∉κ.primeFactors) :
    badCount S T κ K p=baseCount S T κ K-rectCount S T κ K p .plus-
      rectCount S T κ K p .minus+rectCount S T κ K p .both := by
  let _ : Fact p.Prime:=⟨prime⟩
  unfold badCount rectCount baseCount mass
  rw [←sum_sub_distrib,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases hp : clear a p true <;> by_cases hm : clear a p false <;>
    simp [passes,accepts,prime_test a T κ p odd outside aux,hp,hm]

def places (K L : ℕ) : Finset ℕ := (Ioc K L).filter Nat.Prime

theorem mem_places {K L p : ℕ} : p∈places K L ↔ K<p ∧ p≤L ∧ p.Prime := by
  simp [places,and_assoc]

theorem finite_lower (S : Finset (Record A d H Y)) (T : Finset ℕ) (κ K L : ℕ)
    (kl : K≤L) (seven : 7≤K) :
    baseCount S T κ K-(∑ p∈places K L,badCount S T κ K p) ≤ mainMass T κ L S := by
  let U:=baseSet S T κ K
  let P:=places K L
  have union:=surviving_mass P U (fun p a=>¬atPrime a.gaussian T κ p) weight
    (fun a _ => (weight_pos a).le)
  have agree : U.filter (fun a=> ∀ p∈P,¬¬atPrime a.gaussian T κ p)=
      S.filter (fun a=>below a T κ L) := by
    ext a
    simp only [U,baseSet,mem_filter]
    constructor
    · rintro ⟨⟨mem,low⟩,rest⟩
      refine ⟨mem,fun p q odd sev pl=>?_⟩
      by_cases pk : p≤K
      · exact low p q odd sev pk
      · exact Classical.not_not.mp (rest p (mem_places.mpr ⟨by omega,pl,q⟩))
    · rintro ⟨mem,low⟩
      refine ⟨⟨mem,fun p q odd sev pk=>low p q odd sev (pk.trans kl)⟩,?_⟩
      intro p hp
      obtain ⟨big,sm,q⟩:=mem_places.mp hp
      exact not_not_intro (low p q (by omega) (by omega) sm)
  calc
    _ ≤ _ := union
    _ = ∑ a∈U.filter (fun a=>∀ p∈P,¬¬atPrime a.gaussian T κ p),weight a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      split <;> rfl
    _ = _ := congrArg (fun B : Finset (Record A d H Y) => ∑ a∈B,weight a) agree

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.rectangle_test
#print axioms Sun28.SinglePrime.prime_test
#print axioms Sun28.SinglePrime.bad_count
#print axioms Sun28.SinglePrime.finite_lower
