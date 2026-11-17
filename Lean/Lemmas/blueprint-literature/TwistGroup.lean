import KummerRealization

/-! A scaling morphism for the short Weierstrass equation y² = x³ + a x.
It is used below with the embedding Q ↪ Qbar and scale 1/√(−d). -/
namespace ZInQBlueprint.Rank

noncomputable section
open WeierstrassCurve.Affine

section Scaling

private def short {F : Type*} [Field F] (a : F) : WeierstrassCurve.Affine F :=
  (⟨0,0,0,a,0⟩ : WeierstrassCurve F).toAffine

private theorem short_ns {F : Type*} [Field F] (a x y : F) :
    (short a).Nonsingular x y ↔ y^2=x^3+a*x ∧ (0 ≠ 3*x^2+a ∨ y ≠ -y) := by
  simp [nonsingular_iff, equation_iff, short]

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable (f : F →+* K) (a : F) (b k : K) (hk : k ≠ 0) (hb : b=k^4*f a)

omit [DecidableEq F] [DecidableEq K] in
include hk hb in
private theorem scale_ns {x y : F} (h : (short a).Nonsingular x y) :
    (short b).Nonsingular (k^2*f x) (k^3*f y) := by
  rw [short_ns] at h ⊢
  obtain ⟨eqn,regular⟩ := h
  have e := congrArg f eqn
  simp only [map_pow,map_add,map_mul] at e
  constructor
  · rw [hb]
    linear_combination k^6*e
  · rcases regular with hx | hy
    · left
      intro z
      have z' : k^4*f (3*x^2+a)=0 := by
        simpa only [map_add,map_mul,map_ofNat,map_pow] using
          (show k^4*((3:K)*(f x)^2+f a)=0 by rw [hb] at z; linear_combination -z)
      exact hx (by apply f.injective; simpa using ((mul_eq_zero.mp z').resolve_left (pow_ne_zero 4 hk)).symm)
    · right
      intro z
      apply hy
      apply f.injective
      rw [map_neg]
      exact mul_left_cancel₀ (pow_ne_zero 3 hk) (by simpa using z)

include hk hb in
private theorem scale_slope (x₁ x₂ y₁ y₂ : F) :
    (short b).slope (k^2*f x₁) (k^2*f x₂) (k^3*f y₁) (k^3*f y₂) =
      k * f ((short a).slope x₁ x₂ y₁ y₂) := by
  have hx : k^2*f x₁=k^2*f x₂ ↔ x₁=x₂ := by simp [hk,f.injective.eq_iff]
  have hy : k^3*f y₁= -(k^3*f y₂) ↔ y₁= -y₂ := by
    have t : k^3*f y₁ = k^3*f (-y₂) ↔ y₁ = -y₂ :=
        ⟨fun h => f.injective (mul_left_cancel₀ (pow_ne_zero 3 hk) h), fun h => by rw [h]⟩
    simpa only [map_neg,mul_neg] using t
  simp only [WeierstrassCurve.Affine.slope, negY, short, WeierstrassCurve.toAffine, mul_zero, zero_mul, add_zero, sub_zero, hx, hy]
  split_ifs with e₁ e₂
  · simp
  · rw [map_div₀, map_add,map_mul,map_ofNat,map_pow,map_sub,map_neg,hb]
    by_cases hden : f y₁ - -f y₁=0
    · have : k^3*f y₁ - -(k^3*f y₁)=0 := by linear_combination k^3*hden
      simp [hden,this]
    · field_simp [hk,hden]
  · rw [map_div₀,map_sub,map_sub]
    have hden : f x₁ - f x₂ ≠ 0 := sub_ne_zero.mpr (fun h => e₁ (f.injective h))
    field_simp [hk,hden]

private def scalePoint : (short a).Point → (short b).Point
  | .zero => .zero
  | .some h => .some (scale_ns f a b k hk hb h)

omit [DecidableEq F] [DecidableEq K] in
private theorem scaleX (x₁ x₂ m : F) :
    (short b).addX (k^2*f x₁) (k^2*f x₂) (k*f m) = k^2*f ((short a).addX x₁ x₂ m) := by
  simp [addX,short]
  ring

omit [DecidableEq F] [DecidableEq K] in
private theorem scaleY (x₁ x₂ y m : F) :
    (short b).addY (k^2*f x₁) (k^2*f x₂) (k^3*f y) (k*f m) =
      k^3*f ((short a).addY x₁ x₂ y m) := by
  simp [addY,negAddY,addX,negY,short]
  ring

private def scaleHom : (short a).Point →+ (short b).Point where
  toFun := scalePoint f a b k hk hb
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁,y₁,h₁⟩) (_ | @⟨x₂,y₂,h₂⟩)
    any_goals rfl
    have hx : k^2*f x₁=k^2*f x₂ ↔ x₁=x₂ := by simp [hk,f.injective.eq_iff]
    have hy : k^3*f y₁= -(k^3*f y₂) ↔ y₁= -y₂ := by
      have t : k^3*f y₁ = k^3*f (-y₂) ↔ y₁ = -y₂ :=
        ⟨fun h => f.injective (mul_left_cancel₀ (pow_ne_zero 3 hk) h), fun h => by rw [h]⟩
      simpa only [map_neg,mul_neg] using t
    have hxy : (k^2*f x₁=k^2*f x₂ ∧ k^3*f y₁ = (short b).negY (k^2*f x₂) (k^3*f y₂)) ↔
        (x₁=x₂ ∧ y₁=(short a).negY x₂ y₂) := by
      simp only [negY,short,WeierstrassCurve.toAffine,zero_mul,sub_zero,hx,hy]
    by_cases h : x₁=x₂ ∧ y₁=(short a).negY x₂ y₂
    · rw [Point.add_of_Y_eq h.1 h.2]
      have h' := hxy.mpr h
      exact (Point.add_of_Y_eq h'.1 h'.2).symm
    · have h' := mt hxy.mp h
      rw [Point.add_some h]
      change Point.some _ = Point.some _ + Point.some _
      rw [Point.add_some h', Point.some.injEq]
      constructor
      · rw [scale_slope f a b k hk hb, scaleX]
      · rw [scale_slope f a b k hk hb, scaleY]

end Scaling

attribute [local instance] Classical.decEq

/-- The point on the negative twist is rational and has infinite order.
Its image on y²=x³−x is the given anti-invariant point, and the calculation
of the Weierstrass addition law above ensures that the map preserves order
in the direction required here. -/
theorem negativeTwistDescent : NegativeTwistDescent := by
  intro d hd anti
  obtain ⟨u,v,hP,hI⟩ := anti
  let s := sqrtMinus d
  have hs : s^2= -(d:Qbar) := sqrtMinus_sq d
  have hdF : (d:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hdK : (d:Qbar) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hs0 : s ≠ 0 := by
    intro hz
    apply hdK
    simpa [hz] using hs.symm
  have hs4 : s^4=(d:Qbar)^2 := by linear_combination (s^2-(d:Qbar))*hs
  let f : ℚ →+* Qbar := algebraMap ℚ Qbar
  let a : ℚ := -(d:ℚ)^2
  have hb : (-1:Qbar) = (s⁻¹)^4*f a := by
    dsimp [f,a]
    push_cast
    rw [←hs4]
    field_simp
  have hv : v ≠ 0 := by
    intro hz
    apply hI 2 (by decide)
    rw [two_smul]
    exact Point.add_of_Y_eq rfl (by simp [hz,baseCurve,negY])
  have e := ((short_ns (-1:Qbar) _ _).mp hP).1
  change ((v:Qbar)*s)^2 = (u:Qbar)^3+(-1)*(u:Qbar) at e
  have he : -(d:ℚ)*v^2=u^3-u := by
    apply f.injective
    dsimp [f]
    push_cast
    rw [mul_pow,hs] at e
    linear_combination e
  have hr : (short a).Nonsingular (-(d:ℚ)*u) ((d:ℚ)^2*v) := by
    apply (short_ns _ _ _).mpr
    constructor
    · dsimp [a]
      linear_combination (twistEquation_iff (d:ℚ) u v hdF).mp he
    · right
      intro hz
      apply mul_ne_zero (pow_ne_zero 2 hdF) hv
      linarith
  let P : RationalPoint d := .some hr
  refine ⟨P,?_⟩
  let L := scaleHom f a (-1) s⁻¹ (inv_ne_zero hs0) hb
  have hxx : (s⁻¹)^2*f (-(d:ℚ)*u)=(u:Qbar) := by
    dsimp [f]
    push_cast
    rw [←hs]
    field_simp
    rfl
  have hyy : (s⁻¹)^3*f ((d:ℚ)^2*v)=(v:Qbar)*s := by
    dsimp [f]
    push_cast
    rw [←hs4]
    field_simp
    rfl
  have himg : L P = Point.some hP := by
    change Point.some _ = Point.some _
    rw [Point.some.injEq]
    exact ⟨hxx,hyy⟩
  intro m hm hkill
  apply hI m hm
  rw [←himg]
  calc
    _ = L (m • P) := (L.map_nsmul P m).symm
    _ = L 0 := congrArg L hkill
    _ = 0 := L.map_zero

theorem allCoversOfGeometricRow (d : ℕ) (hd : d % 8=5) (hs : Squarefree d)
    (comparison : DeterminantGenusComparison) (tyz : TYZGenusToAntiPoint)
    (eight : EightModTwoOfPositiveRank) (embedding : KummerEmbedding d)
    (pointCover : CoverOfKummerCoordinates) (hsize : (selmer d).ncard=8)
    (row : (smithM5b d).det=1) : ∀ ab ∈ selmer d, cover ℚ d ab.1 ab.2 :=
  allCoversOfRow d hd hs comparison tyz negativeTwistDescent eight embedding pointCover hsize row

end
end ZInQBlueprint.Rank

#print axioms ZInQBlueprint.Rank.negativeTwistDescent
#print axioms ZInQBlueprint.Rank.allCoversOfGeometricRow
