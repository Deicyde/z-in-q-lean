import ZInQKernel.Size.FormalMultiple.Existence
import ZInQKernel.Assembly.Local.FormalMultiplication
import LocalSelection

/-! Rational coefficients at a ramified or unramified prime of ℚ(√2). -/
namespace Sun28.ScalarPlaces
open ZInQ ZInQ.Mult ZInQ.Size ZInQ.Assembly
noncomputable section

/-- Test all primes above an odd prime. At 2 there is a single prime with
ramification index 2, so rational precision k means uniformizer precision 2k. -/
def Deep (p : ℕ) (k : ℤ) (x : K0) : Prop :=
  if p=2 then ((2*k:ℤ):WithTop ℤ)≤vS x
  else ∀ π : Zs, ∀ hπ : Prime π, π∣(p:Zs) → (k:WithTop ℤ)≤vP π hπ x

theorem dyadic_coordinates {k : ℤ} {x : K0} (h : ((2*k:ℤ):WithTop ℤ)≤vS x) :
    (x.re≠0 → k≤padicValRat 2 x.re) ∧ (x.im≠0 → k≤padicValRat 2 x.im) := by
  by_cases hz : x=0
  · subst x; simp
  rw [vP_apply _ hz] at h
  have hv : 2*k≤vp sqrt2Z x := WithTop.coe_le_coe.mp h
  by_cases h₀ : x.re=0
  · have h₁ : x.im≠0 := fun e => hz (K0.ext_iff'.mpr ⟨h₀,e⟩)
    have eq : x=(x.im:K0)*sqrt2 := by ext <;> simp [sqrt2,h₀]
    rw [eq,vS_rat_mul_sqrt2 h₁] at hv
    exact ⟨fun e => False.elim (e h₀),fun _ => by omega⟩
  by_cases h₁ : x.im=0
  · have eq : x=(x.re:K0) := by ext <;> simp [h₁]
    rw [eq,vS_rat h₀] at hv
    exact ⟨fun _ => by omega,fun e => False.elim (e h₁)⟩
  rw [show x=⟨x.re,x.im⟩ from rfl,vS_formula h₀ h₁,le_min_iff] at hv
  obtain ⟨h₁',h₂'⟩ := hv
  exact ⟨fun _ => by omega,fun _ => by omega⟩

theorem deep_coordinates {p : ℕ} [hp : Fact p.Prime] {k : ℤ} {x : K0} (h : Deep p k x) :
    (x.re≠0 → k≤padicValRat p x.re) ∧ (x.im≠0 → k≤padicValRat p x.im) := by
  by_cases dy : p=2
  · subst p
    exact dyadic_coordinates (by simpa [Deep] using h)
  · exact padicValRat_coords_ge dy k x (by simpa [Deep,dy] using h)

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.dyadic_coordinates
#print axioms Sun28.ScalarPlaces.deep_coordinates
