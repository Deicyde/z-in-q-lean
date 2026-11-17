import TYZGenusPoint
import Mathlib.FieldTheory.Galois.Infinite

/-! Tian–Yuan–Zhang, §§3.1 and 3.3. Quadratic descent and the order-two
consequence of the two-cusp identity are proved on the specific elliptic groups. -/
namespace ZInQBlueprint.TYZ.Specialization

noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

abbrev K := Rank.Qbar
abbrev Gal := K ≃ₐ[ℚ] K

/-- Reuse the scaling homomorphism from the pinned twist development at scale one. -/
local macro "shortCurveScaling" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `TwistGroup `ZInQBlueprint.Rank.scaleHom))

/-- The coordinatewise rational Galois action on the target `y² = x³ − x`. -/
def targetAction (σ : Gal) : Rank.baseCurve.toAffine.Point →+ Rank.baseCurve.toAffine.Point :=
  shortCurveScaling σ.toRingHom (-1) (-1) 1 one_ne_zero (by simp)

@[simp] theorem targetAction_coords (σ : Gal) (x y : K) (h : Rank.baseCurve.toAffine.Nonsingular x y) :
    targetCoords (targetAction σ (.some x y h)) = some (σ x, σ y) := by
  change some (1^2 * σ x, 1^3 * σ y) = some (σ x, σ y)
  simp

/-- The source `Y² = X³ + 4X` is also defined over ℚ. -/
def sourceAction (σ : Gal) : genusCurve.toAffine.Point →+ genusCurve.toAffine.Point :=
  shortCurveScaling σ.toRingHom 4 4 1 one_ne_zero (by
    rw [one_pow,one_mul]
    exact (map_natCast σ 4).symm)

private theorem sourceAction_some (σ : Gal) (x y : K) (h : genusCurve.toAffine.Nonsingular x y) :
    ∃ h' : genusCurve.toAffine.Nonsingular (σ x) (σ y),
      sourceAction σ (.some x y h) = .some _ _ h' := by
  cases hp : sourceAction σ (.some x y h) with
  | zero => change Point.some _ _ _ = Point.zero at hp; contradiction
  | some a b hab =>
    change Point.some (1^2 * σ x) (1^3 * σ y) _ = Point.some a b hab at hp
    obtain ⟨ha,hb⟩ := Point.some.inj hp
    simp only [one_pow,one_mul] at ha hb
    subst a
    subst b
    exact ⟨hab,rfl⟩

/-- The absolute Galois action factors on this point through the quadratic
character of ℚ(√−d). This is membership in `E(K_d)⁻`. -/
def GaloisMinus (d : ℕ) (P : Rank.baseCurve.toAffine.Point) : Prop := ∀ σ : Gal,
  targetAction σ P = if σ (Rank.sqrtMinus d) = Rank.sqrtMinus d then P else -P

/-- The selected root is carried to one of the two roots of its quadratic. -/
theorem conjugate_root (σ : Gal) (d : ℕ) :
    σ (Rank.sqrtMinus d) = Rank.sqrtMinus d ∨ σ (Rank.sqrtMinus d) = -Rank.sqrtMinus d := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, Rank.sqrtMinus_sq, map_neg, map_natCast]

/-- An absolute automorphism fixes the specified intermediate field pointwise
exactly when it fixes its chosen square root. -/
theorem fixes_imaginaryField_iff (d : ℕ) (σ : Gal) :
    σ ∈ (Rank.imaginaryField d).fixingSubgroup ↔ σ (Rank.sqrtMinus d) = Rank.sqrtMinus d := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
  · intro h x hx
    apply IntermediateField.adjoin_induction ℚ (motive := fun z _ => σ z = z) _ _ _ _ _ hx
    · intro y hy
      have he := Set.mem_singleton_iff.mp hy
      simpa only [he] using h
    · intro q
      exact σ.commutes q
    · intro y z _ _ hy hz
      rw [map_add, hy, hz]
    · intro y _ hy
      rw [map_inv₀, hy]
    · intro y z _ _ hy hz
      rw [map_mul, hy, hz]

private theorem fixed_is_rational (x : K) (hx : ∀ σ : Gal, σ x = x) : ∃ u : ℚ, (u : K) = x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx

private theorem coords_injective : Function.Injective targetCoords := by
  rintro (_ | ⟨x,y,h⟩) (_ | ⟨x',y',h'⟩) eqn
  · rfl
  · contradiction
  · contradiction
  · simpa only [targetCoords, Option.some.injEq, Prod.mk.injEq, Point.some.injEq] using eqn

/-- Although the construction used the CM endomorphism over ℚ(i), its
combination giving the displayed two-isogeny commutes with every σ over ℚ. -/
theorem isogeny_galois (σ : Gal) (P : genusCurve.toAffine.Point) :
    targetAction σ (tyzIsogeny P) = tyzIsogeny (sourceAction σ P) := by
  cases P with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | some x y h =>
    obtain ⟨h', he⟩ := sourceAction_some σ x y h
    rw [he]
    by_cases hx : x = 0
    · subst x
      simp only [map_zero] at h' ⊢
      rw [tyzIsogeny_at_zero, map_zero, tyzIsogeny_at_zero]
    · have hc := tyzIsogeny_chart hx h
      have hc' := tyzIsogeny_chart (by simpa using σ.injective.ne hx) h'
      cases hi : tyzIsogeny (.some x y h) with
      | zero => rw [hi] at hc; contradiction
      | some r t hr =>
        rw [hi] at hc
        obtain ⟨hrx,hty⟩ : r=(x^2+4)/(4*x) ∧ t=y*(x^2-4)/(8*x^2) := by
          simpa [targetCoords] using hc
        apply coords_injective
        rw [targetAction_coords, hc', hrx, hty]
        have h4 : σ (4:K) = 4 := map_natCast σ 4
        have h8 : σ (8:K) = 8 := map_natCast σ 8
        simp [h4,h8]

private theorem neg_coords (x y : K) (h : Rank.baseCurve.toAffine.Nonsingular x y) :
    targetCoords (-Point.some x y h) = some (x,-y) := by
  rw [Point.neg_some]
  simp [targetCoords, negY, Rank.baseCurve]

/-- Affine descent for TYZ's target, including infinity. -/
theorem minus_iff_coordinates {d : ℕ} (hd : 0 < d) (P : Rank.baseCurve.toAffine.Point) :
    GaloisMinus d P ↔ P = 0 ∨ ∃ (u v : ℚ) (h : Rank.baseCurve.toAffine.Nonsingular
      (u : K) ((v : K) * Rank.sqrtMinus d)), Point.some _ _ h = P := by
  cases P with
  | zero =>
    constructor
    · intro _
      exact Or.inl rfl
    · intro _ σ
      change targetAction σ 0 = if _ then 0 else -0
      rw [map_zero, neg_zero, ite_self]
  | some x y h =>
    have hs : Rank.sqrtMinus d ≠ 0 := by
      intro he
      have hh := Rank.sqrtMinus_sq d
      simp [he] at hh
      omega
    constructor
    · intro H
      have conjugates (σ : Gal) : σ x = x ∧ σ (y / Rank.sqrtMinus d) = y / Rank.sqrtMinus d := by
        have q := congrArg targetCoords (H σ)
        rw [targetAction_coords] at q
        rcases conjugate_root σ d with hf | hf
        · rw [ite_eq_left hf] at q
          have xy : σ x = x ∧ σ y = y := by simpa [targetCoords] using q
          exact ⟨xy.1, by rw [map_div₀, xy.2, hf]⟩
        · by_cases hfixed : σ (Rank.sqrtMinus d) = Rank.sqrtMinus d
          · have wz : Rank.sqrtMinus d = -Rank.sqrtMinus d := hfixed.symm.trans hf
            exact False.elim (hs (by linear_combination wz / 2))
          rw [ite_eq_right hfixed, neg_coords] at q
          have xy : σ x = x ∧ σ y = -y := by simpa using q
          exact ⟨xy.1, by rw [map_div₀, xy.2, hf, neg_div_neg_eq]⟩
      obtain ⟨u, hu⟩ := fixed_is_rational x (fun σ => (conjugates σ).1)
      obtain ⟨v, hv⟩ := fixed_is_rational (y / Rank.sqrtMinus d) (fun σ => (conjugates σ).2)
      have hy : (v : K) * Rank.sqrtMinus d = y := (eq_div_iff hs).mp hv
      subst x
      subst y
      exact Or.inr ⟨u,v,h,rfl⟩
    · rintro (hz | ⟨u,v,h',eqn⟩)
      · contradiction
      obtain ⟨rfl,rfl⟩ := Point.some.inj eqn
      intro σ
      apply coords_injective
      rw [targetAction_coords]
      split_ifs with hfixed
      · simp [targetCoords, hfixed]
      · rw [neg_coords, map_mul, (conjugate_root σ d).resolve_left hfixed]
        simp

#print axioms isogeny_galois
#print axioms conjugate_root
#print axioms fixes_imaginaryField_iff
#print axioms minus_iff_coordinates
end
end ZInQBlueprint.TYZ.Specialization
