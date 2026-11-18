import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Mathlib.Algebra.Field.Rat

/-! The normalized rational cocycle of a family of compatible conjugate isogenies. -/
namespace ZOverQ.Qualitative.CentralIsogenyCocycle
noncomputable section
variable {H G : Type*} [Group H] [Group G]

/-- If conjugation on the kernel is inner, every element of the quotient has
a lift centralizing the entire kernel. -/
theorem central_lift (π : H →* G) (onto : Function.Surjective π)
    (inner : ∀ x : H, ∃ u : H, π u = 1 ∧ ∀ y : H, π y = 1 → x*y*x⁻¹ = u*y*u⁻¹) (g : G) :
    ∃ x : H, π x = g ∧ ∀ y : H, π y = 1 → x*y = y*x := by
  obtain ⟨x,rfl⟩ := onto g
  obtain ⟨u,hu,act⟩ := inner x
  refine ⟨u⁻¹*x, by simp [hu], ?_⟩
  intro y hy
  calc
    (u⁻¹*x)*y = u⁻¹*(x*y*x⁻¹)*x := by group
    _ = u⁻¹*(u*y*u⁻¹)*x := by rw [act y hy]
    _ = y*(u⁻¹*x) := by group

/-- For any coherent group of semilinear automorphisms up to isogeny, the
commuting lifts have rational scalar defects when the centre of the full
endomorphism algebra is rational. The conclusion includes the section and
its multiplication law, so the cocycle is attached to the given lifts. -/
theorem normalized_cocycle (π : H →* G) (onto : Function.Surjective π)
    (inner : ∀ x : H, ∃ u : H, π u = 1 ∧ ∀ y : H, π y = 1 → x*y*x⁻¹ = u*y*u⁻¹)
    (q : ℚˣ →* H) (injective : Function.Injective q)
    (centre : ∀ z : H, π z = 1 → (∀ y : H, π y = 1 → z*y=y*z) → ∃ a : ℚˣ, q a = z)
    (scalars : ∀ a : ℚˣ, π (q a) = 1) :
    ∃ (s : G → H) (c : G × G → ℚˣ), s 1 = 1 ∧ (∀ g, π (s g) = g) ∧
      (∀ g y, π y = 1 → s g*y = y*s g) ∧
      (∀ g h, s g*s h = q (c (g,h))*s (g*h)) ∧
      (∀ g, c (1,g)=1 ∧ c (g,1)=1) ∧
      ∀ g h j, c (g*h,j)*c (g,h) = c (h,j)*c (g,h*j) := by
  classical
  choose lift hπ commute using central_lift π onto inner
  let s (g : G) : H := if g = 1 then 1 else lift g
  have norm : s 1 = 1 := by simp [s]
  have proj (g : G) : π (s g) = g := by by_cases h : g=1 <;> simp [s,h,hπ]
  have central (g : G) (y : H) (hy : π y=1) : s g*y=y*s g := by
    by_cases h : g=1 <;> simp [s,h,commute g y hy]
  let C := Subgroup.centralizer (π.ker : Set H)
  have inside (g : G) : s g ∈ C := fun y hy => (central g y hy).symm
  have defect (g h : G) : ∃ a : ℚˣ, q a = s g*s h*(s (g*h))⁻¹ := by
    apply centre
    · simp [proj]
    · have mem := C.mul_mem (C.mul_mem (inside g) (inside h)) (C.inv_mem (inside (g*h)))
      exact fun y hy => (mem y hy).symm
  choose v hv using defect
  let c (x : G × G) := v x.1 x.2
  have mul (g h : G) : s g*s h = q (c (g,h))*s (g*h) := by
    change s g*s h = q (v g h)*s (g*h)
    rw [hv]
    group
  refine ⟨s,c,norm,proj,central,mul,?_,?_⟩
  · intro g
    constructor <;> apply injective <;> simp [c,hv,norm]
  · intro g h j
    apply injective
    apply mul_right_cancel (b:=s (g*(h*j)))
    calc
      q (c (g*h,j)*c (g,h))*s (g*(h*j)) =
          q (c (g,h))*(q (c (g*h,j))*s ((g*h)*j)) := by
            rw [mul_comm (c (g*h,j)),map_mul,mul_assoc,mul_assoc g h j]
      _ = (s g*s h)*s j := by rw [← mul,← mul_assoc,← mul]
      _ = s g*(q (c (h,j))*s (h*j)) := by rw [mul_assoc,mul h j]
      _ = q (c (h,j))*(s g*s (h*j)) := by rw [← mul_assoc,central g _ (scalars _),mul_assoc]
      _ = q (c (h,j)*c (g,h*j))*s (g*(h*j)) := by rw [mul g (h*j),map_mul,mul_assoc]

end
end ZOverQ.Qualitative.CentralIsogenyCocycle

#print axioms ZOverQ.Qualitative.CentralIsogenyCocycle.central_lift
#print axioms ZOverQ.Qualitative.CentralIsogenyCocycle.normalized_cocycle
