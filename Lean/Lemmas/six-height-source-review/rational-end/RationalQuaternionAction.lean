import QuaternionOrder

/-! Scalar extension of the displayed integral quaternion order. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
open QuaternionAlgebra
noncomputable section

private def e₁ : O := ⟨0, 1, 0, 0⟩
private def e₂ : O := ⟨0, 0, 1, 0⟩
private def e₃ : O := ⟨0, 0, 0, 1⟩

private theorem integral_decomposition (x : O) :
    x.re • (1 : O) + x.imI • e₁ + x.imJ • e₂ + x.imK • e₃ = x := by
  ext <;> simp [e₁, e₂, e₃]

private theorem rational_decomposition (x : B) :
    (x.re-x.imJ) • embed 1 + (2*x.imJ) • embed e₁ +
      (x.imI+x.imK) • embed e₂ + (-2*x.imK) • embed e₃ = x := by
  ext <;> simp [embed,e₁,e₂,e₃] <;> ring

private theorem order_induction {P : B → Prop} (ofOrder : ∀ u, P (embed u))
    (add : ∀ a b, P a → P b → P (a+b))
    (scale : ∀ (t : ℚ) a, P a → P (t • a)) (x : B) : P x := by
  rw [← rational_decomposition x]
  exact add _ _ (add _ _ (add _ _ (scale _ _ (ofOrder 1)) (scale _ _ (ofOrder e₁)))
    (scale _ _ (ofOrder e₂))) (scale _ _ (ofOrder e₃))

variable {D : Type*} [Ring D] [Algebra ℚ D]

private def extend (a : O →+* D) (x : B) : D :=
  (x.re-x.imJ) • (1 : D) + (2*x.imJ) • a e₁ + (x.imI+x.imK) • a e₂ + (-2*x.imK) • a e₃

private theorem extend_embed (a : O →+* D) (x : O) : extend a (embed x) = a x := by
  have h := congrArg a (integral_decomposition x)
  simp only [map_add, map_zsmul, map_one] at h
  unfold extend
  rw [show (embed x).re - (embed x).imJ = (x.re : ℚ) by simp [embed],
      show 2*(embed x).imJ = (x.imI : ℚ) by simp [embed]; ring,
      show (embed x).imI + (embed x).imK = (x.imJ : ℚ) by simp [embed]; ring,
      show -2*(embed x).imK = (x.imK : ℚ) by simp [embed]; ring]
  simpa only [Int.cast_smul_eq_zsmul] using h

private theorem extend_add (a : O →+* D) (x y : B) :
    extend a (x+y) = extend a x + extend a y := by
  unfold extend
  change (x.re+y.re-(x.imJ+y.imJ)) • (1:D) + (2*(x.imJ+y.imJ)) • a e₁ +
    (x.imI+y.imI+(x.imK+y.imK)) • a e₂ + (-2*(x.imK+y.imK)) • a e₃ = _
  have h : x.re+y.re-(x.imJ+y.imJ) = (x.re-x.imJ)+(y.re-y.imJ) := by ring
  have k : x.imI+y.imI+(x.imK+y.imK) = (x.imI+x.imK)+(y.imI+y.imK) := by ring
  rw [h,k]
  simp only [mul_add,add_smul]
  abel

private theorem extend_smul (a : O →+* D) (t : ℚ) (x : B) :
    extend a (t • x) = t • extend a x := by
  simp only [extend,smul_add,smul_smul]
  change (t*x.re-t*x.imJ) • (1:D) + (2*(t*x.imJ)) • a e₁ +
    (t*x.imI+t*x.imK) • a e₂ + (-2*(t*x.imK)) • a e₃ = _
  rw [←mul_sub,←mul_add,mul_left_comm 2 t,mul_left_comm (-2) t]

private theorem extend_mul (a : O →+* D) (x y : B) :
    extend a (x*y) = extend a x * extend a y := by
  refine order_induction (P := fun q => ∀ s, extend a (q*s) = extend a q * extend a s)
    ?_ ?_ ?_ x y
  · intro q s
    refine order_induction (P := fun v => extend a (embed q*v) = extend a (embed q)*extend a v)
      ?_ ?_ ?_ s
    · intro v
      rw [← embed_mul,extend_embed,extend_embed,extend_embed,map_mul]
    · intro v w hv hw
      rw [mul_add,extend_add,extend_add,mul_add,hv,hw]
    · intro t v hv
      rw [Algebra.mul_smul_comm,extend_smul,extend_smul,Algebra.mul_smul_comm,hv]
  · intro v w hv hw s
    rw [add_mul,extend_add,extend_add,add_mul,hv,hw]
  · intro t v hv s
    rw [Algebra.smul_mul_assoc,extend_smul,extend_smul,Algebra.smul_mul_assoc,hv]

/-- The unique rational-algebra action extending an integral action in a
possibly noncommutative rational algebra. -/
def extendRationalAction (a : O →+* D) : B →ₐ[ℚ] D where
  toFun := extend a
  map_zero' := by simp [extend]
  map_one' := by simp [extend]
  map_add' := extend_add a
  map_mul' := extend_mul a
  commutes' t := by simp [extend,QuaternionAlgebra.algebraMap_eq,Algebra.smul_def]

theorem extendRationalAction_embed (a : O →+* D) (x : O) :
    extendRationalAction a (embed x) = a x := extend_embed a x

theorem extendRationalAction_unique (a : O →+* D) (f : B →ₐ[ℚ] D)
    (h : ∀ x, f (embed x) = a x) : f = extendRationalAction a := by
  ext x
  exact order_induction (P := fun y => f y = extendRationalAction a y)
    (fun y => (h y).trans (extendRationalAction_embed a y).symm)
    (fun y z hy hz => by rw [map_add,map_add,hy,hz])
    (fun t y hy => by rw [map_smul,map_smul,hy]) x

end
end ZInQBlueprint.LevelThree.IntegralOrder

#print axioms ZInQBlueprint.LevelThree.IntegralOrder.extendRationalAction
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.extendRationalAction_embed
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.extendRationalAction_unique
