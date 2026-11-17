import TYZCuspRank

/-! The literal compositum of Tian–Yuan–Zhang p. 739 and field of definition of its elliptic points. -/
namespace ZInQBlueprint.TYZ.Specialization

noncomputable section
open WeierstrassCurve.Affine
attribute [local instance] Classical.decEq
abbrev SubfieldQ := IntermediateField ℚ K

/-- The same imaginary unit used in the isogeny. Multiplication by it turns
our chosen square root of −m into a square root of m. -/
def sqrtDivisor (m : ℕ) : K := Rank.sqrtMinus 1 * Rank.sqrtMinus m

theorem sqrtDivisor_sq (m : ℕ) : sqrtDivisor m ^ 2 = (m : K) := by
  simp [sqrtDivisor, mul_pow, Rank.sqrtMinus_sq]

/-- Adjoining the affine coordinates of the modular point `z_m = f_m(P_m)`
to the supplied Hilbert class field, as on pp. 738–739. Infinity has no extra coordinates. -/
def pointField (H : SubfieldQ) (P : A) : SubfieldQ :=
  match P with
  | .zero => H
  | .some x y _ => H ⊔ IntermediateField.adjoin ℚ {x,y}

theorem base_le_pointField (H : SubfieldQ) (P : A) : H ≤ pointField H P := by
  cases P with
  | zero => exact le_rfl
  | some => exact le_sup_left

/-- `L_n(i)` as defined on p. 739. `n.divisors` contains positive divisors. -/
def radicalField (n : ℕ) : SubfieldQ := IntermediateField.adjoin ℚ
  (insert (Rank.sqrtMinus 1) (sqrtDivisor '' (↑n.divisors : Set ℕ)))

/-- The individual fields `H'_m` are supplied by the CM construction. Only
those indexed by positive divisors of classes five and six enter this compositum. -/
def genusCompositum (H' : ℕ → SubfieldQ) (n : ℕ) : SubfieldQ :=
  radicalField n ⊔ (n.divisors.filter fun m => m%8=5 ∨ m%8=6).sup H'

theorem i_mem_compositum (H' : ℕ → SubfieldQ) (n : ℕ) :
    Rank.sqrtMinus 1 ∈ genusCompositum H' n :=
  (show radicalField n ≤ genusCompositum H' n from le_sup_left)
    (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _))

theorem generator_mem_compositum {m n : ℕ} (hm : m ∈ n.divisors) (H' : ℕ → SubfieldQ) :
    sqrtDivisor m ∈ genusCompositum H' n :=
  (show radicalField n ≤ genusCompositum H' n from le_sup_left)
    (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ ⟨m,hm,rfl⟩))

theorem classField_le_compositum {m n : ℕ} (hm : m ∈ n.divisors) (hr : m%8=5 ∨ m%8=6)
    (H' : ℕ → SubfieldQ) : H' m ≤ genusCompositum H' n :=
  (Finset.le_sup (f := H') (Finset.mem_filter.mpr ⟨hm,hr⟩)).trans le_sup_right

/-- Divisibility makes the compositum increase. -/
theorem compositum_mono {m n : ℕ} (hm : m ∣ n) (hn : n ≠ 0) (H' : ℕ → SubfieldQ) :
    genusCompositum H' m ≤ genusCompositum H' n := by
  have sub (t : ℕ) (ht : t ∈ m.divisors) : t ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp ht).1.trans hm,hn⟩
  apply sup_le
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx|⟨t,ht,rfl⟩)
    · rw [hx]; exact i_mem_compositum H' n
    · exact generator_mem_compositum (sub t ht) H'
  · apply Finset.sup_le
    intro t ht
    obtain ⟨ht,hr⟩ := Finset.mem_filter.mp ht
    exact classField_le_compositum (sub t ht) hr H'

/-- The group of points of A over F, inside the geometric elliptic group. -/
def pointsOver (F : SubfieldQ) : AddSubgroup A where
  carrier := {P | ∀ σ : Gal, σ ∈ F.fixingSubgroup → sourceAction σ P = P}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := by intro P Q hP hQ σ hσ; rw [map_add,hP σ hσ,hQ σ hσ]
  neg_mem' := by intro P hP σ hσ; rw [map_neg,hP σ hσ]

private theorem sourceAction_some_eq (σ : Gal) (x y : K) (h : genusCurve.toAffine.Nonsingular x y) :
    sourceAction σ (.some x y h) = .some x y h ↔ σ x = x ∧ σ y = y := by
  change Point.some (1^2 * σ x) (1^3 * σ y) _ = Point.some x y h ↔ _
  erw [Point.some.injEq]
  simp

/-- The fixed-point definition agrees with the usual affine field of definition. -/
theorem some_mem_pointsOver (F : SubfieldQ) (x y : K) (h : genusCurve.toAffine.Nonsingular x y) :
    Point.some x y h ∈ pointsOver F ↔ x ∈ F ∧ y ∈ F := by
  change (∀ σ : Gal, σ ∈ F.fixingSubgroup → sourceAction σ (.some x y h) = .some x y h) ↔ _
  simp only [sourceAction_some_eq]
  have iff_fixed (a : K) : a ∈ F ↔ ∀ σ : Gal, σ ∈ F.fixingSubgroup → σ a = a := by
    conv_lhs => rw [←InfiniteGalois.fixedField_fixingSubgroup F]
    exact IntermediateField.mem_fixedField_iff _ _
  rw [iff_fixed x,iff_fixed y]
  exact ⟨fun H => ⟨fun σ hσ => (H σ hσ).1, fun σ hσ => (H σ hσ).2⟩,
    fun H σ hσ => ⟨H.1 σ hσ,H.2 σ hσ⟩⟩

/-- `H(P)` is the smallest intermediate field containing `H` over which `P` is rational. -/
theorem pointField_le_iff (H F : SubfieldQ) (P : A) :
    pointField H P ≤ F ↔ H ≤ F ∧ P ∈ pointsOver F := by
  cases P with
  | zero =>
    change H ≤ F ↔ H ≤ F ∧ (0:A) ∈ pointsOver F
    simp [(pointsOver F).zero_mem]
  | some x y h =>
    rw [pointField, sup_le_iff, IntermediateField.adjoin_le_iff, some_mem_pointsOver]
    simp [Set.insert_subset_iff,Set.singleton_subset_iff]

theorem pointsOver_mono {F F' : SubfieldQ} (hF : F ≤ F') : pointsOver F ≤ pointsOver F' := by
  intro P hP
  cases P with
  | zero => exact (pointsOver F').zero_mem
  | some x y h =>
    obtain ⟨hx,hy⟩ := (some_mem_pointsOver F x y h).mp hP
    exact (some_mem_pointsOver F' x y h).mpr ⟨hF hx,hF hy⟩

/-- The complex multiplication `[i]` with affine formula `(X,Y) ↦ (−X,iY)`. -/
local macro "tyzCMI" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `TYZIsogeny `ZInQBlueprint.TYZ.cmI))

def multiplyI : A →+ A := tyzCMI

private theorem multiplyI_some (x y : K) (h : genusCurve.toAffine.Nonsingular x y) :
    ∃ h' : genusCurve.toAffine.Nonsingular (-x) (Rank.sqrtMinus 1 * y),
    multiplyI (.some x y h) = Point.some _ _ h' := by
  have sq : (-(Rank.sqrtMinus 1))^2 = -1 := by simpa using Rank.sqrtMinus_sq 1
  have cube : (-(Rank.sqrtMinus 1))^3 = Rank.sqrtMinus 1 := by linear_combination -Rank.sqrtMinus 1 * sq
  cases hp : multiplyI (.some x y h) with
  | zero => change Point.some _ _ _ = Point.zero at hp; contradiction
  | some a b hab =>
    change Point.some ((-Rank.sqrtMinus 1)^2*x) ((-Rank.sqrtMinus 1)^3*y) _ = Point.some a b hab at hp
    obtain ⟨ha,hb⟩ := Point.some.inj hp
    rw [sq,neg_one_mul] at ha
    rw [cube] at hb
    subst a; subst b
    exact ⟨hab,rfl⟩

theorem multiplyI_mem {F : SubfieldQ} (hi : Rank.sqrtMinus 1 ∈ F) {P : A} (hP : P ∈ pointsOver F) :
    multiplyI P ∈ pointsOver F := by
  cases P with
  | zero => exact (map_zero multiplyI) ▸ (pointsOver F).zero_mem
  | some x y h =>
    obtain ⟨hx,hy⟩ := (some_mem_pointsOver F x y h).mp hP
    obtain ⟨h',he⟩ := multiplyI_some x y h
    rw [he]
    exact (some_mem_pointsOver F _ _ h').mpr ⟨F.neg_mem hx,F.mul_mem hi hy⟩

/-- The four roots of unity occurring as the epsilon factors on page 739. -/
inductive GaussianUnit where | one | negOne | i | negI

def GaussianUnit.act (e : GaussianUnit) (P : A) : A :=
  match e with
  | .one => P
  | .negOne => -P
  | .i => multiplyI P
  | .negI => -(multiplyI P)

theorem GaussianUnit.act_mem (e : GaussianUnit) {F : SubfieldQ} (hi : Rank.sqrtMinus 1 ∈ F)
    {P : A} (hP : P ∈ pointsOver F) : e.act P ∈ pointsOver F := by
  cases e with
  | one => exact hP
  | negOne => exact (pointsOver F).neg_mem hP
  | i => exact multiplyI_mem hi hP
  | negI => exact (pointsOver F).neg_mem (multiplyI_mem hi hP)

#print axioms sqrtDivisor_sq
#print axioms pointField_le_iff
#print axioms classField_le_compositum
#print axioms compositum_mono
#print axioms some_mem_pointsOver
#print axioms pointsOver_mono
#print axioms multiplyI_mem
#print axioms GaussianUnit.act_mem
end
end ZInQBlueprint.TYZ.Specialization
