import AlternatingTwo

namespace Sun28.Corank
noncomputable section

/-- Standard arithmetic data. At every level the actual Kummer maps form a short
exact sequence. The cofinite-primary structure describes the Sha term as the
torsion in the divisible part and in one fixed finite reduced group. The
alternating pairing is specified on the latter, not on its elements of order two. -/
structure PrimaryData (A : Type) [AddCommGroup A] where
  sel : ℕ → Type
  [groupSel : ∀ j, AddCommGroup (sel j)]
  reduced : Type
  [groupReduced : AddCommGroup reduced]
  [finiteReduced : Finite reduced]
  d : ℕ
  bounded : ∃ j : ℕ, ∀ x : reduced, (2^j : ℕ) • x=0
  values : Type
  [groupValues : AddCommGroup values]
  pair : reduced →+ reduced →+ values
  alternating : ∀ x, pair x x=0
  nondegenerate : ∀ x, (∀ y, pair x y=0) → x=0
  kummer : ∀ j, quotientAt A (2^j) →+ sel j
  boundary : ∀ j, sel j →+ (Fin d → ZMod (2^j)) × torsionAt reduced (2^j)
  injective : ∀ j, Function.Injective (kummer j)
  surjective : ∀ j, Function.Surjective (boundary j)
  exactness : ∀ j, (kummer j).range=(boundary j).ker

attribute [instance] PrimaryData.groupSel PrimaryData.groupReduced PrimaryData.finiteReduced
  PrimaryData.groupValues

theorem layer_count {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T]
    (K : PrimaryData A) {r : ℕ} (split : A ≃+ (Fin r → ℤ) × T) (j : ℕ) :
    Nat.card (K.sel j) = Nat.card (torsionAt A (2^j)) *
      (2^j)^(r+K.d) * Nat.card (torsionAt K.reduced (2^j)) := by
  let : NeZero (2^j : ℕ) := ⟨by positivity⟩
  rw [exact_count (K.kummer j) (K.boundary j) (K.injective j) (K.surjective j) (K.exactness j),
    quotient_growth split (by positivity),Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_zmod,
    pow_add]
  ac_rfl

/-- Dimension three forces the entire reduced primary group to vanish. -/
theorem corank_one {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T]
    (K : PrimaryData A) {r : ℕ} (split : A ≃+ (Fin r → ℤ) × T)
    (tors : Nat.card (torsionAt A 2)=4) (eight : Nat.card (K.sel 1)=8) :
    Subsingleton K.reduced ∧ r + K.d = 1 := by
  have e := layer_count K split 1
  rw [pow_one,tors,eight] at e
  have u : 0 < (2:ℕ)^(r+K.d) := by positivity
  have few : Nat.card (torsionAt K.reduced 2) ≤ 2 := by
    nlinarith only [e, Nat.mul_le_mul_right (Nat.card (torsionAt K.reduced 2)) u]
  let : Subsingleton K.reduced := reduced_trivial K.bounded K.pair K.alternating K.nondegenerate few
  have h : Nat.card (torsionAt K.reduced 2)=1 := Nat.card_unique
  rw [h,mul_one] at e
  have powEq : (2:ℕ)^(r+K.d)=2^1 := by omega
  exact ⟨inferInstance,(Nat.pow_right_injective (by decide : 2≤2)) powEq⟩

theorem all_higher_card {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T]
    (K : PrimaryData A) {r : ℕ} (split : A ≃+ (Fin r → ℤ) × T)
    (tors : Nat.card (torsionAt A 2)=4) (eight : Nat.card (K.sel 1)=8) (j : ℕ) :
    Nat.card (K.sel j) = Nat.card (torsionAt A (2^j)) * 2^j := by
  obtain ⟨hs,hd⟩ := corank_one K split tors eight
  let := hs
  have h : Nat.card (torsionAt K.reduced (2^j)) = 1 := Nat.card_unique
  rw [layer_count K split,hd,pow_one,h,mul_one]

theorem finite_sha_forces_rank_one {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T]
    (K : PrimaryData A) {r : ℕ} (split : A ≃+ (Fin r → ℤ) × T)
    (tors : Nat.card (torsionAt A 2)=4) (eight : Nat.card (K.sel 1)=8) :
    K.d=0 ↔ r=1 := by
  have e := (corank_one K split tors eight).2
  omega

end
end Sun28.Corank

#print axioms Sun28.Corank.layer_count
#print axioms Sun28.Corank.corank_one
#print axioms Sun28.Corank.all_higher_card
#print axioms Sun28.Corank.finite_sha_forces_rank_one
