import Mathlib.Tactic

/-! Arithmetic-normalized coefficients of homogeneous binary forms and generators of GL₂. -/
namespace ZInQBlueprint.MarkedForm
noncomputable section
variable {K : Type*} [Field K]
abbrev Coeff (K : Type*) (n : ℕ) := Fin (n+1) → K

/-- The entries are the coefficients after removal of their binomial factors. -/
def evalF {n : ℕ} (f : Coeff K n) (x z : K) : K :=
  ∑ i : Fin (n+1), (n.choose i.val:K)*f i*x^i.val*z^(n-i.val)

/-- Homogeneous coefficient expansion detects equality over any infinite field of
characteristic zero. -/
theorem ext_form [CharZero K] [Infinite K] {n : ℕ} (f g : Coeff K n)
    (h : ∀ x z, evalF f x z=evalF g x z) : f=g := by
  classical
  let p (v : Coeff K n) : Polynomial K :=
    ∑ i : Fin (n+1), Polynomial.monomial i.val ((n.choose i.val:K)*v i)
  have ev (v : Coeff K n) (x : K) : (p v).eval x=evalF v x 1 := by
    simp [p,evalF,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  have he : p f=p g := Polynomial.funext fun x => (ev f x).trans ((h x 1).trans (ev g x).symm)
  have cf (v : Coeff K n) (i : Fin (n+1)) : (p v).coeff i.val=(n.choose i.val:K)*v i := by
    simp [p,Polynomial.coeff_monomial,Fin.val_inj]
  funext i
  have eq := congrArg (fun q:Polynomial K => q.coeff i.val) he
  rw [cf,cf] at eq
  have hn : (n.choose i.val:K)≠0 := by exact_mod_cast (Nat.choose_pos (by omega : i.val≤n)).ne'
  exact mul_left_cancel₀ hn eq

inductive Change (K : Type*) where
  | shift (h : K)
  | swap
  | diag (p q : K)
deriving Inhabited

def xy (g : Change K) (x z : K) : K×K :=
  match g with
  | .shift h => (x+h*z,z)
  | .swap => (z,x)
  | .diag p q => (p*x,q*z)

def det (g : Change K) : K :=
  match g with
  | .shift _ => 1
  | .swap => -1
  | .diag p q => p*q

/-- The three generator substitutions in degree 2. -/
def act2 (g : Change K) (f : Coeff K 2) : Coeff K 2 :=
  match g with
  | .shift h => ![f 0+2*h*f 1+h^2*f 2, f 1+h*f 2, f 2]
  | .swap => ![f 2, f 1, f 0]
  | .diag p q => ![q^2*f 0, p*q*f 1, p^2*f 2]

theorem eval_act2 (g : Change K) (f : Coeff K 2) (x z : K) :
    evalF (act2 g f) x z=evalF f (xy g x z).1 (xy g x z).2 := by
  cases g <;> simp [act2,evalF,xy,Fin.sum_univ_succ,Fin.succ,Nat.choose] <;> ring

/-- The three generator substitutions in degree 4. -/
def act4 (g : Change K) (f : Coeff K 4) : Coeff K 4 :=
  match g with
  | .shift h => ![f 0+4*h*f 1+6*h^2*f 2+4*h^3*f 3+h^4*f 4, f 1+3*h*f 2+3*h^2*f 3+h^3*f 4, f 2+2*h*f 3+h^2*f 4, f 3+h*f 4, f 4]
  | .swap => ![f 4, f 3, f 2, f 1, f 0]
  | .diag p q => ![q^4*f 0, p*q^3*f 1, p^2*q^2*f 2, p^3*q*f 3, p^4*f 4]

theorem eval_act4 (g : Change K) (f : Coeff K 4) (x z : K) :
    evalF (act4 g f) x z=evalF f (xy g x z).1 (xy g x z).2 := by
  cases g <;> simp [act4,evalF,xy,Fin.sum_univ_succ,Fin.succ,Nat.choose] <;> ring

/-- The three generator substitutions in degree 6. -/
def act6 (g : Change K) (f : Coeff K 6) : Coeff K 6 :=
  match g with
  | .shift h => ![f 0+6*h*f 1+15*h^2*f 2+20*h^3*f 3+15*h^4*f 4+6*h^5*f 5+h^6*f 6, f 1+5*h*f 2+10*h^2*f 3+10*h^3*f 4+5*h^4*f 5+h^5*f 6, f 2+4*h*f 3+6*h^2*f 4+4*h^3*f 5+h^4*f 6, f 3+3*h*f 4+3*h^2*f 5+h^3*f 6, f 4+2*h*f 5+h^2*f 6, f 5+h*f 6, f 6]
  | .swap => ![f 6, f 5, f 4, f 3, f 2, f 1, f 0]
  | .diag p q => ![q^6*f 0, p*q^5*f 1, p^2*q^4*f 2, p^3*q^3*f 3, p^4*q^2*f 4, p^5*q*f 5, p^6*f 6]

theorem eval_act6 (g : Change K) (f : Coeff K 6) (x z : K) :
    evalF (act6 g f) x z=evalF f (xy g x z).1 (xy g x z).2 := by
  cases g <;> simp [act6,evalF,xy,Fin.sum_univ_succ,Fin.succ,Nat.choose] <;> ring

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.ext_form
#print axioms ZInQBlueprint.MarkedForm.eval_act2
#print axioms ZInQBlueprint.MarkedForm.eval_act4
#print axioms ZInQBlueprint.MarkedForm.eval_act6
