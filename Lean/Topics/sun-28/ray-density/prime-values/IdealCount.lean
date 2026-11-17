import IdealOrientation
import UnweightedRows

namespace Sun28.PrimeValues
open Sun28.Reciprocity Sun28.FinitePattern Sun28.CutoffCount Sun28.ContactFactors Finset
noncomputable section
open scoped Classical

private def fromOrientation {L p : ℕ} (h : Bool × Oriented L p) : Unoriented L p :=
  match h with
  | (false,⟨J,n,a⟩) => ⟨J,n,(class_of_opposite J).2 (Or.inl a)⟩
  | (true,⟨J,n,a⟩) => ⟨opposite J,(opposite_data J).2.1.trans n,
      (class_of_opposite _).2 (Or.inr ((opposite_twice J).symm ▸ a))⟩

private theorem opposite_distinct {L : ℕ} {J K:Ideals L}
    (a:admissible L (word J)) (b:admissible L (word K)) : J≠opposite K := by
  rintro rfl
  have e:= (opposite_data K).2.2
  exact disjoint_conjugates b (e ▸ a)

def conjugatePair (L p : ℕ) : Bool × Oriented L p ≃ Unoriented L p := by
  apply Equiv.ofBijective fromOrientation
  constructor
  · rintro ⟨u,⟨J,n,a⟩⟩ ⟨v,⟨K,m,b⟩⟩
    cases u <;> cases v <;> intro e
    · have h : J=K := congrArg Subtype.val e
      cases h
      rfl
    · exact False.elim (opposite_distinct a b (congrArg Subtype.val e))
    · exact False.elim (opposite_distinct b a (congrArg Subtype.val e.symm))
    · have h : opposite J=opposite K := congrArg Subtype.val e
      have j : J=K := by simpa only [opposite_twice] using congrArg opposite h
      cases j
      rfl
  · rintro ⟨J,n,c⟩
    rcases (class_of_opposite J).1 c with a|b
    · exact ⟨(false,⟨J,n,a⟩),rfl⟩
    · exact ⟨(true,⟨opposite J,(opposite_data J).2.1.trans n,b⟩),Subtype.ext (opposite_twice _)⟩

theorem oriented_card {L p : ℕ} (hp:p.Prime) (above:L<p) (away:p≠7) :
    Nat.card (Oriented L p) = if commonPrime L L p then 1 else 0 := by
  let := oriented_subsingleton (L:=L) hp
  split
  next good =>
    obtain ⟨_,J,n,a⟩ := (commonPrime_iff_ideal above away).1 good
    let : Nonempty (Oriented L p) := ⟨⟨J,n,a⟩⟩
    exact Nat.card_unique
  next bad =>
    let : IsEmpty (Oriented L p) := ⟨fun x => bad (selected_to_integer hp ⟨x.val,x.property⟩)⟩
    exact Nat.card_of_isEmpty

theorem unoriented_card {L p : ℕ} (hp:p.Prime) (above:L<p) (away:p≠7) :
    Nat.card (Unoriented L p) = if commonPrime L L p then 2 else 0 := by
  rw [←Nat.card_congr (conjugatePair L p),Nat.card_prod,oriented_card hp above away]
  split <;> simp

/-- Number of full tuples of Gaussian prime ideals in the accepted conjugacy classes,
over the literal values of the integer forms. Primality is imposed before counting. -/
def idealTuples (A : Fin 3→ℚ) (L : ℕ) (q : ℕ×ℕ) : ℕ :=
  ∏ i : ↥(shifts A), if (form A q i).toNat.Prime then Nat.card (Unoriented L (form A q i).toNat) else 0

theorem tuple_multiplicity {A : Fin 3→ℚ} {L : ℕ} {q : ℕ×ℕ}
    (large : ∀ i : ↥(shifts A),max L 7 < (form A q i).toNat) :
    idealTuples A L q = if ∀ i : ↥(shifts A),0 ≤ form A q i ∧ commonPrime L L (form A q i).toNat
      then 2^(shifts A).card else 0 := by
  have point (i : ↥(shifts A)) : (if (form A q i).toNat.Prime then Nat.card (Unoriented L (form A q i).toNat) else 0) =
      if 0≤form A q i ∧ commonPrime L L (form A q i).toNat then 2 else 0 := by
    let p := (form A q i).toNat
    have a : L<p := (le_max_left ..).trans_lt (large i)
    have b : 7<p := (le_max_right ..).trans_lt (large i)
    have non : 0 ≤ form A q i := by dsimp [p] at b;omega
    by_cases hp : p.Prime
    · simpa [p,hp,non] using unoriented_card hp a (by omega)
    · have ng : ¬commonPrime L L p := fun h => hp h.1
      simp_all [p]
  unfold idealTuples
  simp_rw [point]
  split
  next all => simp [all]
  next fail =>
    push Not at fail
    obtain ⟨i,no⟩:=fail
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    split
    next h => exact (no h.1 h.2).elim
    next => rfl

theorem integer_box_multiplicity {A : Fin 3→ℚ} {d L N W : ℕ}
    (large : ∀ q ∈ Ioc (N/2) N ×ˢ Icc 1 W,∀ i : ↥(shifts A),max L 7 < (form A q i).toNat) :
    (∑ q ∈ (Ioc (N/2) N ×ˢ Icc 1 W).filter (fun q : ℕ×ℕ=>d∣q.2),idealTuples A L q)
      = 2^(shifts A).card * count A d L N W := by
  unfold count
  rw [Finset.card_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hit
  rw [tuple_multiplicity (large q (mem_filter.mp hit).1)]
  split <;> simp

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.conjugatePair
#print axioms Sun28.PrimeValues.oriented_card
#print axioms Sun28.PrimeValues.unoriented_card
#print axioms Sun28.PrimeValues.tuple_multiplicity
#print axioms Sun28.PrimeValues.integer_box_multiplicity
