import QuaternionOrder
import Mathlib.GroupTheory.Coset.Card

/-! Frames of the left regular module and the two Weil-multiplier components. -/
namespace ZInQBlueprint.LevelThree

def multiplier : A →* F where
  toFun := nrd
  map_one' := by simp [nrd_slots]
  map_mul' := nrd_mul

def normOne : Subgroup Aˣ := (Units.map multiplier).ker

theorem mem_normOne (u : Aˣ) : u ∈ normOne ↔ nrd (u:A) = 1 := by
  change Units.map multiplier u = 1 ↔ _
  exact Units.ext_iff

/-- With no chosen multiplier every unit occurs; otherwise fix its value in F₃. -/
def inFibre (c : Option F) (x : A) : Prop :=
  nrd x ≠ 0 ∧ match c with | none => True | some a => nrd x = a

instance (c : Option F) (x : A) : Decidable (inFibre c x) := by
  cases c <;> unfold inFibre <;> infer_instance

abbrev Fibre (c : Option F) := {x : A // inFibre c x}

def positive (x : A) := x.re = 1 ∨ (x.re = 0 ∧ x.imI = 1)
instance (x : A) : Decidable (positive x) := by unfold positive; infer_instance

abbrev Representatives (c : Option F) := {x : A // inFibre c x ∧ positive x}

private theorem inFibre_neg (c : Option F) (x : A) : inFibre c (-x) ↔ inFibre c x := by
  cases c <;> simp [inFibre,nrd_neg]

private theorem signs_complement (x : A) (hx : nrd x ≠ 0) : positive x ↔ ¬positive (-x) := by
  have h : ∀ a b:F, a^2-2*b^2 ≠ 0 →
      ((a=1 ∨ (a=0 ∧ b=1)) ↔ ¬(-a=1 ∨ (-a=0 ∧ -b=1))) := by decide
  exact h x.re x.imI (by rwa [← nrd_slots])

/-- The actual scalar ± orbit relation on a multiplier fibre. -/
def scalarSigns (c : Option F) : Setoid (Fibre c) where
  r x y := x.val = y.val ∨ x.val = -y.val
  iseqv := ⟨fun _ => Or.inl rfl, by
    intro x y h
    rcases h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h]; simp)
    , by
    intro x y z h k
    rcases h with h|h <;> rcases k with k|k <;> simp [h,k]⟩

noncomputable def signedEquiv (c : Option F) : Representatives c ≃ Quotient (scalarSigns c) := by
  let f : Representatives c → Quotient (scalarSigns c) :=
    fun x => Quotient.mk _ ⟨x.val,x.property.1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hh := Quotient.exact h
    change x.val=y.val ∨ x.val = -y.val at hh
    rcases hh with h|h
    · exact Subtype.ext h
    · have hx := x.property.2
      rw [h] at hx
      exact ((signs_complement _ y.property.1.1).mp y.property.2 hx).elim
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases h : positive x.val
    · exact ⟨⟨x.val,x.property,h⟩,rfl⟩
    · have hn : positive (-x.val) := by by_contra hn; exact h ((signs_complement _ x.property.1).mpr hn)
      refine ⟨⟨-x.val,(inFibre_neg c x.val).mpr x.property,hn⟩, Quotient.sound (Or.inr rfl)⟩

theorem raw_counts : Nat.card (Fibre none) = 72 ∧ Nat.card (Fibre (some 1)) = 36 ∧
    Nat.card (Fibre (some (-1))) = 36 := by
  simp only [Nat.card_eq_fintype_card]
  decide

theorem signed_counts : Nat.card (Quotient (scalarSigns none)) = 36 ∧
    Nat.card (Quotient (scalarSigns (some 1))) = 18 ∧
    Nat.card (Quotient (scalarSigns (some (-1)))) = 18 := by
  rw [← Nat.card_congr (signedEquiv none), ← Nat.card_congr (signedEquiv (some 1)),
    ← Nat.card_congr (signedEquiv (some (-1)))]
  simp only [Nat.card_eq_fintype_card]
  decide

noncomputable def unitsEquiv : Aˣ ≃ Fibre none where
  toFun u := ⟨u.val,(unit_iff _).mp u.isUnit,trivial⟩
  invFun x := ((unit_iff _).mpr x.property.1).unit
  left_inv u := Units.ext (IsUnit.unit_spec _)
  right_inv x := Subtype.ext (((unit_iff x.val).mpr x.property.1).unit_spec)

noncomputable def normOneEquiv : normOne ≃ Fibre (some 1) where
  toFun u := ⟨u.val.val,(unit_iff _).mp u.val.isUnit,(mem_normOne _).mp u.property⟩
  invFun x := ⟨((unit_iff _).mpr x.property.1).unit,(mem_normOne _).mpr (by simpa using x.property.2)⟩
  left_inv u := Subtype.ext (Units.ext (IsUnit.unit_spec _))
  right_inv x := Subtype.ext (((unit_iff x.val).mpr x.property.1).unit_spec)

theorem unit_count : Nat.card Aˣ = 72 := (Nat.card_congr unitsEquiv).trans raw_counts.1
theorem normOne_count : Nat.card normOne = 36 := (Nat.card_congr normOneEquiv).trans raw_counts.2.1

theorem symplectic_iff_normOne (u : Aˣ) :
    (∀ x y : A, pairing (x*u.val) (y*u.val) = pairing x y) ↔ u ∈ normOne := by
  rw [mem_normOne]
  constructor
  · intro h
    have hh := h 1 ⟨0,0,1,0⟩
    rw [pairing_change, show pairing (1:A) ⟨0,0,1,0⟩ = 1 by decide, mul_one] at hh
    exact hh
  · intro hu x y
    rw [pairing_change,hu,one_mul]

theorem symplectic_image_dvd {G : Type*} [Group G] (ρ : G →* Aˣ)
    (h : ∀ g x y, pairing (x*(ρ g).val) (y*(ρ g).val) = pairing x y) :
    Nat.card ρ.range ∣ 36 := by
  rw [← normOne_count]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨g,rfl⟩
  exact (symplectic_iff_normOne _).mp (h g)

section Frames
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

private theorem regular_formula (h : R ≃ₗ[R] R) (x : R) : h x = x*h 1 := by
  calc
    h x = h (x • (1:R)) := by simp
    _ = x*h 1 := h.map_smul x 1

/-- No commutativity assumption on R. Left-linear maps of its regular module act on the right. -/
def regularUnitsEquiv : Rˣ ≃ (R ≃ₗ[R] R) where
  toFun u := u.mulRightLinearEquiv R
  invFun h := ⟨h 1,h.symm 1,by rw [← regular_formula h.symm, h.symm_apply_apply],
    by rw [← regular_formula h, h.apply_symm_apply]⟩
  left_inv u := Units.ext (by simp)
  right_inv h := by ext x; exact (regular_formula h x).symm

noncomputable def frameOfBasis (b : Module.Basis Unit R M) : R ≃ₗ[R] M :=
  (Module.Basis.singleton Unit R).equiv b (Equiv.refl Unit)

theorem frame_torsor (e f : R ≃ₗ[R] M) :
    ∃! u : Rˣ, (u.mulRightLinearEquiv R).trans e = f := by
  let h := f.trans e.symm
  obtain ⟨u, hu⟩ := (regularUnitsEquiv (R:=R)).surjective h
  change u.mulRightLinearEquiv R = h at hu
  refine ⟨u,?_,?_⟩
  · change (u.mulRightLinearEquiv R).trans e = f
    rw [hu]
    ext x; simp [h]
  · intro v hv
    apply (regularUnitsEquiv (R:=R)).injective
    change v.mulRightLinearEquiv R = u.mulRightLinearEquiv R
    rw [hu]
    ext x
    apply e.injective
    simpa [h] using congrArg (fun w : R ≃ₗ[R] M => w x) hv

/-- A one-element basis gives a frame, and the unit taking it to any other is unique. -/
theorem frames_of_rank_one (b : Module.Basis Unit R M) :
    ∃ e : R ≃ₗ[R] M, ∀ f : R ≃ₗ[R] M, ∃! u : Rˣ, (u.mulRightLinearEquiv R).trans e = f :=
  ⟨frameOfBasis b,frame_torsor _⟩
end Frames

#print axioms signedEquiv
#print axioms raw_counts
#print axioms signed_counts
#print axioms unit_count
#print axioms normOne_count
#print axioms symplectic_iff_normOne
#print axioms symplectic_image_dvd
#print axioms regularUnitsEquiv
#print axioms frame_torsor
#print axioms frames_of_rank_one
end ZInQBlueprint.LevelThree
