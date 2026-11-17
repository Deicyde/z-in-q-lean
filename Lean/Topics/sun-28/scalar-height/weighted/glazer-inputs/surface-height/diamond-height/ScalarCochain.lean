import MarkedScalarTower
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- A cochain trivializing a normalized factor system inflated from Q.
Only the two normalization identities enter the restriction argument. -/
structure InflatedSplitting {G Q K:Type*} [Group G] [Group Q] [CommGroup K] (q:G →* Q) where
  b : G → K
  factor : Q → Q → K
  left_one : ∀ a, factor 1 a=1
  right_one : ∀ a, factor a 1=1
  split : ∀ x y, b x*b y=factor (q x) (q y)*b (x*y)

variable {G Q K : Type*} [Group G] [Group Q] [CommGroup K] {q : G →* Q}

def InflatedSplitting.restrict (F : InflatedSplitting (K:=K) q) : q.ker →* K where
  toFun x := F.b x
  map_one' := by
    have h:=F.split 1 1
    simp only [map_one,F.left_one,one_mul,mul_one] at h
    exact mul_left_cancel (show F.b 1*F.b 1=F.b 1*1 by simpa using h)
  map_mul' x y := by
    have h:=F.split x.val y.val
    rw [(show q x.val=1 from x.property),F.left_one,one_mul] at h
    exact h.symm

theorem InflatedSplitting.restrict_conjugate (F : InflatedSplitting (K:=K) q)
    (g:G) (x y:q.ker) (conj : y.val=g*x.val*g⁻¹) : F.restrict y=F.restrict x := by
  have a:=F.split g x.val
  rw [(show q x.val=1 from x.prop),F.right_one,one_mul] at a
  have b:=F.split y.val g
  rw [(show q y.val=1 from y.prop),F.left_one,one_mul,conj,inv_mul_cancel_right] at b
  change F.b y.val=F.b x.val
  rw [conj]
  exact mul_right_cancel (b.trans (a.symm.trans (mul_comm ..)))

/-- Pointwise lifts of the chosen character through squaring exist over ℂ. -/
theorem square_lift (χ : G →* ℂˣ) : ∃ u : G → ℂˣ, ∀ g, (u g)^2=χ g := by
  classical
  have lift (g:G) : ∃ u:ℂˣ, u^2=χ g := by
    obtain ⟨z,h⟩:=IsAlgClosed.exists_pow_nat_eq ((χ g):ℂ) (show 0<2 by decide)
    have nz : z≠0:=by intro bad;rw [bad,zero_pow (by decide : 2≠0)] at h;exact (χ g).ne_zero h.symm
    exact ⟨Units.mk0 z nz,Units.ext h⟩
  exact ⟨fun g=>Classical.choose (lift g),fun g=>Classical.choose_spec (lift g)⟩

/-- If a sign correction identifies the two normalized cocycles, multiplying
the chosen roots by that correction solves both equations in (LR2). -/
theorem corrected_splitting (q:G →* Q) (χ:G →* ℂˣ) (m:ℕ)
    (order : ∀ g,(χ g)^m=1) (c:Q → Q → ℂˣ)
    (left : ∀ x,c 1 x=1) (right : ∀ x,c x 1=1) (u s:G → ℂˣ)
    (root : ∀ x,(u x)^2=χ x) (sign : ∀ x,(s x)^2=1)
    (boundary : ∀ x y, (u x*u y/u (x*y))*((s x*s y)/s (x*y))=c (q x) (q y)) :
    ∃ F : InflatedSplitting (K:=ℂˣ) q, F.factor=c ∧ (∀ x,(F.b x)^2=χ x) ∧
      ∀ x,(F.b x)^(2*m)=1 := by
  let F : InflatedSplitting (K:=ℂˣ) q := {
    b:=fun x=>u x*s x
    factor:=c
    left_one:=left
    right_one:=right
    split:=fun x y=>by
      rw [← boundary x y]
      rw [div_mul_div_comm,div_mul_cancel]
      ac_rfl }
  have sq (x:G) : (F.b x)^2=χ x := by change (u x*s x)^2=χ x;rw [mul_pow,root,sign,mul_one]
  exact ⟨F,rfl,sq,fun x=>by rw [pow_mul,sq,order]⟩

/-- After the normalized global sign splitting, the marking-field character,
its conjugation invariance and both local-order factors are consequences. -/
def scalarTower_of_cochain {R:ℕ} (L:IntermediateField ℚ Qbar) [IsGalois ℚ L] [FiniteDimensional ℚ L]
    (degree : Module.finrank ℚ L≤576)
    (F : InflatedSplitting (K:=ℂˣ) (AlgEquiv.restrictNormalHom L : GQ →* (L ≃ₐ[ℚ] L)))
    (dy:GQ →* ℂˣ) (dy2 : ∀ g, (dy g)^2=1)
    (ι : ∀ p:ℕ, GQ →* (ZMod p)ˣ) (χ : ∀ p:ℕ, (ZMod p)ˣ →* ℂˣ)
    (square : ∀ g, (F.b g)^2 = dy g * ∏ p ∈ R.primeFactors, χ p (ι p g))
    (det:GQ →* ℂˣ) (det2:∀ g ∈ F.restrict.ker.map (markingGroup L).subtype, (det g)^2=1) :
    ScalarTower R :=
  scalarTower_of_local_characters L degree dy dy2 ι χ F.restrict
    (fun x => square x.val) F.restrict_conjugate det det2

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.InflatedSplitting.restrict_conjugate
#print axioms ZInQBlueprint.DiamondHeight.square_lift
#print axioms ZInQBlueprint.DiamondHeight.corrected_splitting
#print axioms ZInQBlueprint.DiamondHeight.scalarTower_of_cochain
