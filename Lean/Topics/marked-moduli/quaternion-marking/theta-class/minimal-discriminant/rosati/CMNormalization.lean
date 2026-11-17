import SixCanonicalPeriods

/-! Choosing the arithmetic coordinate in Baba--Granath, Proposition 3.9,
by the exact value of Errthum's normalized coordinate at discriminant -19. -/
namespace ZInQBlueprint.ShimuraAtlas
noncomputable section

/-- The signed entry for discriminant -19 in Errthum's Table 2. -/
def cm19Coordinate : ℚ := -(3^7 : ℚ) / 2^10

theorem cm19_in_absolute_table :
    ((-19, 3^7, 2^10) : QuaternionLift.CMRow) ∈ QuaternionLift.rationalCMRows ∧
      |cm19Coordinate| = QuaternionLift.absoluteCoordinate (-19, 3^7, 2^10) := by
  constructor
  · decide +kernel
  · norm_num [cm19Coordinate, QuaternionLift.absoluteCoordinate]

/-- The normalized arithmetic and analytic coordinates agree globally.
Their alternative reciprocal relation would already fail at the -19 point.
The product formulation is needed only there and allows a pole elsewhere. -/
theorem normalized_eq_of_cm19 {X : Type*} (T t : X → ℂ) (p : X)
    (alternatives : T = t ∨ ∀ x, t x ≠ 0 → T x * t x = 1)
    (arithmetic : T p = -(27 : ℂ) / 16 * (81 / 64))
    (modular : t p = (cm19Coordinate : ℂ)) : T = t := by
  rcases alternatives with eq | reciprocal
  · exact eq
  · have nz : t p ≠ 0 := by rw [modular]; norm_num [cm19Coordinate]
    have wrong := reciprocal p nz
    rw [arithmetic, modular] at wrong
    norm_num [cm19Coordinate] at wrong

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.ShimuraAtlas
open CategoryTheory

/-- If the composition on the elliptic product B is multiplication by two,
every doubled integral endomorphism of B intertwines with an integral
endomorphism on the Jacobian A. -/
theorem twice_endomorphism {C : Type*} [Category C] [Preadditive C]
    {A B : C} (f : A ⟶ B) (g : B ⟶ A) (comp : g ≫ f = (2 : ℤ) • 𝟙 B)
    (b : B ⟶ B) : ∃ a : A ⟶ A, a ≫ f = (2 : ℤ) • (f ≫ b) := by
  refine ⟨f ≫ b ≫ g, ?_⟩
  simp only [Category.assoc, comp, Preadditive.comp_zsmul, Category.comp_id]

/-- Two complementary elliptic quotients give the double of each central
integer. A local integral representative at two gives an odd multiple.
The central order then contains the integer itself. -/
theorem full_of_twice_and_at_two {G : Type*} [AddCommGroup G] (L : AddSubgroup G)
    (twice : ∀ x : G, (2 : ℤ) • x ∈ L)
    (atTwo : ∀ x : G, ∃ k : ℤ, (2*k+1) • x ∈ L) : L = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k, hk⟩ := atTwo x
  have he : (2*k+1) • x - k • ((2 : ℤ) • x) = x := by
    rw [add_zsmul, one_zsmul, show (2 : ℤ)*k = k*2 by ring, mul_zsmul]
    abel
  exact he ▸ L.sub_mem hk (L.zsmul_mem (twice x) k)

end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.cm19_in_absolute_table
#print axioms ZInQBlueprint.ShimuraAtlas.normalized_eq_of_cm19
#print axioms ZInQBlueprint.ShimuraAtlas.twice_endomorphism
#print axioms ZInQBlueprint.ShimuraAtlas.full_of_twice_and_at_two
