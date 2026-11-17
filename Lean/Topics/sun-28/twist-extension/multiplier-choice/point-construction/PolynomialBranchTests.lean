import SquareFamilySpecialization

namespace Sun28.PointConstruction
open Filter RatFunc Sun28.Ordinary Sun28.ScalarHeight Sun28.PrescribedPoints
noncomputable section

/-- A pair of rational functions fixes the two free abscissas; its square roots remain free. -/
structure WitnessRow where
  multiplier : ℚ
  listed : multiplier ∈ smallMultipliers
  first : Functions
  ratio : Functions

namespace WitnessRow
variable (r : WitnessRow)

def A := C r.multiplier * genericB
def H := r.A*(r.A-genericB^2)
def guard := r.A*r.first*r.H*r.ratio
def leftRad := r.A*(r.A-r.first)*(r.A+3*r.first)
def rightRad := r.A*(r.A*r.ratio^2-r.first*r.H)*(r.A*r.ratio^2+3*(r.first*r.H))

theorem nonsquare_choice (active : r.guard ≠ 0) :
    ¬IsSquare r.leftRad ∨ ¬IsSquare r.rightRad := by
  by_contra! both
  obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩:=both
  exact no_scalar_function_branch r.listed ⟨r.first,r.ratio,active,y,z,
    by simpa only [leftRad,A,pow_two] using hy.symm,by simpa only [rightRad,H,A,pow_two] using hz.symm⟩

private theorem germB : evaluate genericB = (↑inputB:Germs) := by
  rw [map_mul,map_pow,evaluate_constant,evaluate_variable];rfl

/-- Any passing rational specialization gives a nonzero guard and two squares. -/
theorem specialization : ∀ᶠ x:ℚ in cofinite, poleBranch r.multiplier (inputB x)
    (value r.first x) (value r.ratio x) →
    value r.guard x ≠ 0 ∧ IsSquare (value r.leftRad x) ∧ IsSquare (value r.rightRad x) := by
  let a (x:ℚ):=r.multiplier*inputB x
  let h (x:ℚ):=a x*(a x-(inputB x)^2)
  have ha : evaluate r.A=(↑a:Germs) := by
    dsimp only [A];rw [map_mul,evaluate_constant,germB];rfl
  have hh : evaluate r.H=(↑h:Germs) := by
    dsimp only [H];rw [map_mul,map_sub,map_pow,ha,germB];rfl
  have gd : (value r.guard) =ᶠ[cofinite] (fun x => a x*value r.first x*h x*value r.ratio x) := by
    apply Germ.coe_eq.mp
    change evaluate r.guard=_
    simp only [guard,map_mul,ha,hh];rfl
  have lm : (value r.leftRad) =ᶠ[cofinite] (fun x =>
      a x*(a x-value r.first x)*(a x+3*value r.first x)) := by
    apply Germ.coe_eq.mp
    change evaluate r.leftRad=_
    simp only [leftRad,map_mul,map_add,map_sub,map_ofNat,ha];rfl
  have rm : (value r.rightRad) =ᶠ[cofinite] (fun x =>
      a x*(a x*(value r.ratio x)^2-value r.first x*h x)*
        (a x*(value r.ratio x)^2+3*(value r.first x*h x))) := by
    apply Germ.coe_eq.mp
    change evaluate r.rightRad=_
    simp only [rightRad,map_mul,map_pow,map_add,map_sub,map_ofNat,ha,hh];rfl
  filter_upwards [gd,lm,rm] with x hg hl hr ok
  obtain ⟨nz,y,z,ys,zs⟩:=ok
  refine ⟨hg.symm ▸ nz,⟨y,?_⟩,⟨z,?_⟩⟩
  · rw [hl];simpa only [←pow_two] using ys.symm
  · rw [hr];simpa only [a,h,←pow_two,mul_assoc] using zs.symm

end WitnessRow
end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.WitnessRow.nonsquare_choice
#print axioms Sun28.PointConstruction.WitnessRow.specialization
