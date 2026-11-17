import OrdinaryFibreBridge

/-! The Mestre conic splits on the six-contact family. A rational point of
the R₃ parameter line need not admit a rational sextic representative. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.ShimuraAtlas
open CoarseConic SexticInvariants QuaternionLift
noncomputable section

/-- The diagonalized Mestre conic in Baba–Granath, equation (3.3). -/
def MestreSplit (j : ℚ) : Prop :=
  ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x^2+6*j*y^2+2*(27*j+16)*z^2 = 0

/-- A rational point on every nonexceptional member of the signed family. -/
theorem six_contact_mestre_split {u : ℚ} (hu : u ∉ ZInQ.contactSet) : MestreSplit (SixContact.J u) := by
  refine ⟨8*r u*h u,4*h u,r u,Or.inr (Or.inr (radical_units hu).1),?_⟩
  linear_combination 96*(h u)^2*(first_square u) - 2*(r u)^2*(second_square u)

private theorem mod_seven (a b : ZMod 7) (h : -(24:ZMod 7)*a^2+8*b^2=0) : a=0 ∧ b=0 :=
  (by decide : ∀ a b : ZMod 7, -(24:ZMod 7)*a^2+8*b^2=0 → a=0 ∧ b=0) a b h

private theorem integer_descent (n : ℕ) :
    ∀ x y z : ℤ, x.natAbs+y.natAbs+z.natAbs=n → 7*x^2-24*y^2+8*z^2=0 → x=0 ∧ y=0 ∧ z=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y z size eq
    have residual : -(24:ZMod 7)*(y:ZMod 7)^2+8*(z:ZMod 7)^2=0 := by
      have red := congrArg (fun k : ℤ => (k : ZMod 7)) eq
      push_cast at red
      simpa only [show (7:ZMod 7)=0 from by decide,zero_mul,zero_sub,neg_mul] using red
    obtain ⟨b,hb⟩ : (7:ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y 7).mp (mod_seven _ _ residual).1
    obtain ⟨c,hc⟩ : (7:ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 7).mp (mod_seven _ _ residual).2
    have first : x^2=168*b^2-56*c^2 := by rw [hb,hc] at eq; nlinarith only [eq]
    have xzero : (x:ZMod 7)^2=0 := by
      have red := congrArg (fun k : ℤ => (k : ZMod 7)) first
      push_cast at red
      simpa only [show (168:ZMod 7)=0 from by decide,show (56:ZMod 7)=0 from by decide,
        zero_mul,sub_zero] using red
    obtain ⟨a,ha⟩ : (7:ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 7).mp (sq_eq_zero_iff.mp xzero)
    have divided : 7*a^2-24*b^2+8*c^2=0 := by rw [ha,hb,hc] at eq; nlinarith only [eq]
    have size' : 7*a.natAbs+7*b.natAbs+7*c.natAbs=n := by
      simpa only [ha,hb,hc,Int.natAbs_mul,show (7:ℤ).natAbs=7 from rfl] using size
    by_cases small : a.natAbs+b.natAbs+c.natAbs=0
    · have a0 : a=0 := Int.natAbs_eq_zero.mp (by omega)
      have b0 : b=0 := Int.natAbs_eq_zero.mp (by omega)
      have c0 : c=0 := Int.natAbs_eq_zero.mp (by omega)
      simp [ha,hb,hc,a0,b0,c0]
    · obtain ⟨a0,b0,c0⟩ := ih _ (by omega : a.natAbs+b.natAbs+c.natAbs<n) a b c rfl divided
      simp [ha,hb,hc,a0,b0,c0]

private theorem numerator_eq (q : ℚ) : (q.num : ℚ) = q*(q.den : ℚ) :=
  (div_eq_iff (by exact_mod_cast q.den_nz)).mp q.num_div_den

/-- The punctured R₃ chart has t=1 and j=−4/7, but the corresponding
Mestre conic is anisotropic at 7, hence has no rational point. -/
theorem mestre_nonsplit_at_unit_slope : ¬ MestreSplit (-4/7) := by
  rintro ⟨x,y,z,nonzero,eq⟩
  have baseEq : 7*x^2-24*y^2+8*z^2=0 := by linear_combination 7*eq
  let k : ℚ := (x.den:ℚ)*(y.den:ℚ)*(z.den:ℚ)
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast x.den_nz)
    (by exact_mod_cast y.den_nz)) (by exact_mod_cast z.den_nz)
  let X : ℤ := x.num*y.den*z.den
  let Y : ℤ := y.num*x.den*z.den
  let Z : ℤ := z.num*x.den*y.den
  have hx : (X:ℚ)=x*k := by dsimp [X,k]; push_cast; rw [numerator_eq x]; ring
  have hy : (Y:ℚ)=y*k := by dsimp [Y,k]; push_cast; rw [numerator_eq y]; ring
  have hz : (Z:ℚ)=z*k := by dsimp [Z,k]; push_cast; rw [numerator_eq z]; ring
  have integral : 7*X^2-24*Y^2+8*Z^2=0 := by
    have rational : 7*(X:ℚ)^2-24*(Y:ℚ)^2+8*(Z:ℚ)^2=0 := by
      rw [hx,hy,hz]; linear_combination k^2*baseEq
    exact_mod_cast rational
  obtain ⟨hX,hY,hZ⟩ := integer_descent _ X Y Z rfl integral
  rcases nonzero with p|p|p
  · exact (mul_ne_zero p hk) (by simp only [←hx,hX,Int.cast_zero])
  · exact (mul_ne_zero p hk) (by simp only [←hy,hY,Int.cast_zero])
  · exact (mul_ne_zero p hk) (by simp only [←hz,hZ,Int.cast_zero])

theorem unit_slope_coordinate : (-16/((1:ℚ)^2+27)) = -4/7 := by norm_num

/-- Necessity in Mestre reconstruction, specialized to the discriminant-six
diagonal form of Baba–Granath (3.3) and Proposition 3.13. -/
def MestreDescentNecessary : Prop :=
  ∀ j : ℚ, j*(64*j-81)*(27*j+16) ≠ 0 → RealizedD6Point j → MestreSplit j

theorem unit_slope_unrealized (criterion : MestreDescentNecessary) : ¬ RealizedD6Point (-4/7) :=
  fun realization => mestre_nonsplit_at_unit_slope (criterion _ (by norm_num) realization)

/-- At an unrealized residue class the rational sextic classification imposes
no value on the reader. -/
theorem classifier_change_unrealized {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) {j : ℚ} (h : ¬ RealizedD6Point j)
    (newRead : IgusaCoordinates → ModuliClass)
    (unchanged : ∀ v, v ≠ bgCoordinates j → newRead v = read v) :
    PolarizedIgusaClassification newRead := by
  intro f degree sep D proper smooth integral chart b A e m P v w hw coordinates
  have other : v ≠ bgCoordinates j := by
    rintro rfl
    exact h ⟨f,w,degree,sep,hw,coordinates⟩
  rw [unchanged _ other]
  exact classification f degree sep D chart b A e m P v w hw coordinates

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.six_contact_mestre_split
#print axioms ZInQBlueprint.ShimuraAtlas.mestre_nonsplit_at_unit_slope
#print axioms ZInQBlueprint.ShimuraAtlas.unit_slope_coordinate
#print axioms ZInQBlueprint.ShimuraAtlas.unit_slope_unrealized
#print axioms ZInQBlueprint.ShimuraAtlas.classifier_change_unrealized
