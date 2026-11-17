import FilteredLogarithm

/-! Restriction of a local elliptic formal logarithm along a field embedding. -/
namespace Sun28.Scalar
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

private def coordZ (W : WeierstrassCurve.Affine L) : W.Point → L
  | .zero => 0
  | .some x y _ => -x/y

private def coordInv (W : WeierstrassCurve.Affine L) : W.Point → L
  | .zero => 0
  | .some x _ _ => x⁻¹

/-- Base change of the elliptic group law along a field embedding, with a target
curve over the new field even when the embedding is twisted by an automorphism. -/
private noncomputable def pointMap (f : K →+* L) (W : WeierstrassCurve.Affine K) :
    W.Point →+ (W.map f).Point where
  toFun Q := match Q with
    | .zero => 0
    | .some x y h => .some (f x) (f y) ((W.map_nonsingular f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁,y₁,h₁⟩) (_ | ⟨x₂,y₂,h₂⟩)
    any_goals rfl
    by_cases hxy : x₁=x₂ ∧ y₁=W.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2,add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2,WeierstrassCurve.Affine.map_negY])]
    · simpa only [add_some hxy,←WeierstrassCurve.Affine.map_addX,←WeierstrassCurve.Affine.map_addY,
        ←WeierstrassCurve.Affine.map_slope] using!
        (add_some (W:=W.map f) (h₁:=(W.map_nonsingular f.injective x₁ y₁).mpr h₁)
           (h₂:=(W.map_nonsingular f.injective x₂ y₂).mpr h₂)
           fun h => hxy ⟨f.injective h.1,f.injective ((W.map_negY f ..) ▸ h.2)⟩).symm

private def pointCongr {W V : WeierstrassCurve.Affine L} (h : W=V) : W.Point →+ V.Point := by
  subst V
  exact AddMonoidHom.id _

private theorem congr_coords {W V : WeierstrassCurve.Affine L} (h : W=V) (Q : W.Point) :
    coordZ V (pointCongr h Q)=coordZ W Q ∧ coordInv V (pointCongr h Q)=coordInv W Q := by
  subst V
  exact ⟨rfl,rfl⟩

omit [DecidableEq K] [DecidableEq L] in
private theorem mapped_curve (f : K →+* L) (b : K) : (curve b).map f = curve (f b) := by
  simp [curve,WeierstrassCurve.map]

noncomputable def mapShortPoint (f : K →+* L) (b : K) : (curve b).Point →+ (curve (f b)).Point :=
  (pointCongr (mapped_curve f b)).comp (pointMap f (curve b))

/-- The maps on both affine coordinates used by the scalar preserve our convention at infinity. -/
theorem mapShortPoint_coordinates (f : K →+* L) {b : K} (Q : (curve b).Point) :
    parameter (mapShortPoint f b Q)=f (parameter Q) ∧
    reciprocal (mapShortPoint f b Q)=f (reciprocal Q) := by
  have h := congr_coords (mapped_curve f b) (pointMap f (curve b) Q)
  have z_eq (T : (curve (f b)).Point) : parameter T = coordZ _ T := by cases T <;> rfl
  have i_eq (T : (curve (f b)).Point) : reciprocal T = coordInv _ T := by cases T <;> rfl
  rw [z_eq,i_eq]
  unfold mapShortPoint
  simp only [AddMonoidHom.comp_apply]
  rw [h.1,h.2]
  cases Q with
  | zero => simp [coordZ,coordInv,pointMap,parameter,reciprocal]
  | some x y h => simp [coordZ,coordInv,pointMap,parameter,reciprocal]

/-- Pulling back a completed-field logarithm needs no equality about pairs of global multiples. -/
noncomputable def pullback_filteredLog {w : AddValuation K (WithTop ℤ)}
    {v : AddValuation L (WithTop ℤ)} {b : K}
    (f : K →+* L) (agrees : ∀ x, v (f x)=w x) (C : FilteredLogarithm v v (f b)) :
    FilteredLogarithm w v b where
  kernel := C.kernel.comap (mapShortPoint f b)
  formal {Q} h nz := by
    apply C.formal
    · rw [(mapShortPoint_coordinates f Q).2,agrees]
      exact h
    · rw [(mapShortPoint_coordinates f Q).1]
      exact (map_ne_zero f).mpr nz
  log := C.log.comp {
    toFun := fun Q => ⟨mapShortPoint f b Q.1,Q.2⟩
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  level Q r hr := by
    change _ ≤ v (C.log ⟨mapShortPoint f b Q.1,Q.2⟩) ↔ _
    rw [C.level ⟨mapShortPoint f b Q.1,Q.2⟩ r hr,(mapShortPoint_coordinates f Q.1).1,agrees]

end Sun28.Scalar
#print axioms Sun28.Scalar.mapShortPoint_coordinates
#print axioms Sun28.Scalar.pullback_filteredLog
