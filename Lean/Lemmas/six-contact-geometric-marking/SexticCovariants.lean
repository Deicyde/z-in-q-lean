import BinaryChanges

/-! Three quadratic covariants of the sextic, obtained by alternating contraction.
Binomial coefficients are incorporated in the coefficient convention of BinaryChanges. -/
namespace ZInQBlueprint.MarkedForm
noncomputable section
variable {K : Type*} [Field K]

def scale {n : ℕ} (a : K) (f : Coeff K n) : Coeff K n := fun i => a*f i

/-- Three times the fully symmetrized fourth transvectant of f and itself. -/
def quartic (f : Coeff K 6) : Coeff K 4 :=
  ![3*(f 0*f 4 - 4*f 1*f 3 + 6*f 2*f 2 - 4*f 3*f 1 + f 4*f 0),
    3*(f 0*f 5 - 4*f 1*f 4 + 6*f 2*f 3 - 4*f 3*f 2 + f 4*f 1),
    (f 0*f 6 - 4*f 1*f 5 + 6*f 2*f 4 - 4*f 3*f 3 + f 4*f 2) + 2*(f 1*f 5 - 4*f 2*f 4 + 6*f 3*f 3 - 4*f 4*f 2 + f 5*f 1),
    3*(f 1*f 6 - 4*f 2*f 5 + 6*f 3*f 4 - 4*f 4*f 3 + f 5*f 2),
    3*(f 2*f 6 - 4*f 3*f 5 + 6*f 4*f 4 - 4*f 5*f 3 + f 6*f 2)]

/-- The full sixth contraction is the quadratic invariant of the sextic. -/
def invariant (f : Coeff K 6) : K :=
  f 0*f 6 - 6*f 1*f 5 + 15*f 2*f 4 - 20*f 3*f 3 + 15*f 4*f 2 - 6*f 5*f 1 + f 6*f 0

/-- The fourth transvectant of a sextic and quartic. -/
def contract64 (f : Coeff K 6) (v : Coeff K 4) : Coeff K 2 :=
  ![f 0*v 4 - 4*f 1*v 3 + 6*f 2*v 2 - 4*f 3*v 1 + f 4*v 0,
    f 1*v 4 - 4*f 2*v 3 + 6*f 3*v 2 - 4*f 4*v 1 + f 5*v 0,
    f 2*v 4 - 4*f 3*v 3 + 6*f 4*v 2 - 4*f 5*v 1 + f 6*v 0]

/-- The second transvectant of a quartic and quadratic. -/
def contract42 (v : Coeff K 4) (q : Coeff K 2) : Coeff K 2 :=
  ![v 0*q 2 - 2*v 1*q 1 + v 2*q 0,
    v 1*q 2 - 2*v 2*q 1 + v 3*q 0,
    v 2*q 2 - 2*v 3*q 1 + v 4*q 0]

set_option maxHeartbeats 2000000 in
theorem quartic_cov (g : Change K) (f : Coeff K 6) :
    quartic (act6 g f)=scale ((det g)^4) (act4 g (quartic f)) := by
  funext i
  cases g <;> fin_cases i <;> dsimp [act6,act4,quartic,scale,det] <;> ring

theorem invariant_cov (g : Change K) (f : Coeff K 6) :
    invariant (act6 g f)=(det g)^6*invariant f := by
  cases g <;> dsimp [invariant,act6,det] <;> ring

set_option maxHeartbeats 2000000 in
theorem contract64_cov (g : Change K) (f : Coeff K 6) (v : Coeff K 4) :
    contract64 (act6 g f) (act4 g v)=scale ((det g)^4) (act2 g (contract64 f v)) := by
  funext i
  cases g <;> fin_cases i <;> dsimp [act6,act4,act2,contract64,scale,det] <;> ring

theorem contract42_cov (g : Change K) (v : Coeff K 4) (q : Coeff K 2) :
    contract42 (act4 g v) (act2 g q)=scale ((det g)^2) (act2 g (contract42 v q)) := by
  funext i
  cases g <;> fin_cases i <;> dsimp [act4,act2,contract42,scale,det] <;> ring

theorem quartic_scale (a : K) (f : Coeff K 6) :
    quartic (scale a f)=scale (a^2) (quartic f) := by
  funext i; fin_cases i <;> dsimp [quartic,scale] <;> ring

theorem invariant_scale (a : K) (f : Coeff K 6) :
    invariant (scale a f)=a^2*invariant f := by dsimp [invariant,scale]; ring

theorem contract64_scale (a b : K) (f : Coeff K 6) (v : Coeff K 4) :
    contract64 (scale a f) (scale b v)=scale (a*b) (contract64 f v) := by
  funext i; fin_cases i <;> dsimp [contract64,scale] <;> ring

theorem contract42_scale (a b : K) (v : Coeff K 4) (q : Coeff K 2) :
    contract42 (scale a v) (scale b q)=scale (a*b) (contract42 v q) := by
  funext i; fin_cases i <;> dsimp [contract42,scale] <;> ring

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.quartic_cov
#print axioms ZInQBlueprint.MarkedForm.invariant_cov
#print axioms ZInQBlueprint.MarkedForm.contract64_cov
#print axioms ZInQBlueprint.MarkedForm.contract42_cov
