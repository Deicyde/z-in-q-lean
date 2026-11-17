import SexticCovariants

/-! Relative invariants and three weighted covariant rows for every linear substitution. -/
namespace ZInQBlueprint.MarkedForm
noncomputable section
variable {K : Type*} [Field K]

def q₁ (f : Coeff K 6) := contract64 f (quartic f)
def q₂ (f : Coeff K 6) := contract42 (quartic f) (q₁ f)
def q₃ (f : Coeff K 6) := contract42 (quartic f) (q₂ f)

/-- The compensating invariant makes all three rows have degree seven in f. -/
def rows (f : Coeff K 6) : Fin 3 → Coeff K 2 :=
  ![scale ((invariant f)^2) (q₁ f),scale (invariant f) (q₂ f),q₃ f]

theorem scale_comp {n : ℕ} (a b : K) (f : Coeff K n) : scale a (scale b f)=scale (a*b) f := by
  funext i; exact (mul_assoc _ _ _).symm

@[simp] theorem scale_one' {n : ℕ} (f : Coeff K n) : scale 1 f=f := by funext i; simp [scale]

theorem scale_eq {n : ℕ} {a b:K} (h:a=b) (f:Coeff K n) : scale a f=scale b f := by rw [h]

theorem act2_scale (g : Change K) (c : K) (q : Coeff K 2) :
    act2 g (scale c q)=scale c (act2 g q) := by
  funext j; cases g <;> fin_cases j <;> dsimp [act2,scale] <;> ring

theorem eval_scale {n : ℕ} (c : K) (f : Coeff K n) (x z : K) :
    evalF (scale c f) x z=c*evalF f x z := by
  unfold evalF scale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem q₁_cov (g : Change K) (f : Coeff K 6) :
    q₁ (act6 g f)=scale ((det g)^8) (act2 g (q₁ f)) := by
  unfold q₁
  rw [quartic_cov,← scale_one' (act6 g f),contract64_scale,one_mul,contract64_cov,scale_comp]
  exact scale_eq (by ring) _

private theorem q₂_cov (g : Change K) (f : Coeff K 6) :
    q₂ (act6 g f)=scale ((det g)^14) (act2 g (q₂ f)) := by
  unfold q₂
  rw [quartic_cov,q₁_cov,contract42_scale,contract42_cov,scale_comp]
  exact scale_eq (by ring) _

private theorem q₃_cov (g : Change K) (f : Coeff K 6) :
    q₃ (act6 g f)=scale ((det g)^20) (act2 g (q₃ f)) := by
  unfold q₃
  rw [quartic_cov,q₂_cov,contract42_scale,contract42_cov,scale_comp]
  exact scale_eq (by ring) _

theorem rows_cov (g : Change K) (f : Coeff K 6) (i:Fin 3) :
    rows (act6 g f) i=scale ((det g)^20) (act2 g (rows f i)) := by
  fin_cases i <;> dsimp [rows]
  · rw [invariant_cov,q₁_cov,act2_scale,scale_comp,scale_comp]
    exact scale_eq (by ring) _
  · rw [invariant_cov,q₂_cov,act2_scale,scale_comp,scale_comp]
    exact scale_eq (by ring) _
  · exact q₃_cov g f

theorem rows_scale (c : K) (f : Coeff K 6) (i:Fin 3) :
    rows (scale c f) i=scale (c^7) (rows f i) := by
  have a : q₁ (scale c f)=scale (c^3) (q₁ f) := by
    unfold q₁; rw [quartic_scale,contract64_scale]; exact scale_eq (by ring) _
  have b : q₂ (scale c f)=scale (c^5) (q₂ f) := by
    unfold q₂; rw [quartic_scale,a,contract42_scale]; exact scale_eq (by ring) _
  have d : q₃ (scale c f)=scale (c^7) (q₃ f) := by
    unfold q₃; rw [quartic_scale,b,contract42_scale]; exact scale_eq (by ring) _
  fin_cases i <;> dsimp [rows]
  · rw [invariant_scale,a,scale_comp,scale_comp]; exact scale_eq (by ring) _
  · rw [invariant_scale,b,scale_comp,scale_comp]; exact scale_eq (by ring) _
  · exact d

inductive Word (K : Type*) where
  | one
  | comp (g : Change K) (rest : Word K)

def point : Word K → K → K → K×K
  | .one,x,z => (x,z)
  | .comp g w,x,z => let b:=xy g x z; point w b.1 b.2

def delta : Word K → K
  | .one => 1
  | .comp g w => det g*delta w

def sexticAction : Word K → Coeff K 6 → Coeff K 6
  | .one,f => f
  | .comp g w,f => act6 g (sexticAction w f)

theorem sextic_action_eval (w : Word K) (f : Coeff K 6) (x z : K) :
    evalF (sexticAction w f) x z=evalF f (point w x z).1 (point w x z).2 := by
  induction w generalizing x z with
  | one => rfl
  | comp g w ih => rw [sexticAction,eval_act6,ih]; rfl

theorem row_action_eval (w : Word K) (f : Coeff K 6) (i:Fin 3) (x z:K) :
    evalF (rows (sexticAction w f) i) x z=
      (delta w)^20 * evalF (rows f i) (point w x z).1 (point w x z).2 := by
  induction w generalizing x z with
  | one => simp [sexticAction,point,delta]
  | comp g w ih =>
    rw [sexticAction,rows_cov,eval_scale,eval_act2,ih]
    simp only [delta,point,mul_pow,mul_assoc]

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.rows_cov
#print axioms ZInQBlueprint.MarkedForm.rows_scale
#print axioms ZInQBlueprint.MarkedForm.sextic_action_eval
#print axioms ZInQBlueprint.MarkedForm.row_action_eval
