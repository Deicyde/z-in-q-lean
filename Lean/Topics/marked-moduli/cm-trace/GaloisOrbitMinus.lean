import TYZGaussianTorsion
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! Descent modulo torsion on the actual TYZ target. For a rank test, the multiple
of the point which descends to the twist may be chosen after the point is given. -/
namespace ZInQBlueprint.TYZ.Specialization
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine
abbrev E := Rank.baseCurve.toAffine.Point

/-- All rational Galois conjugates of a geometric affine point form a finite set. -/
theorem finite_target_orbit (P : E) : (Set.range fun σ : Gal => targetAction σ P).Finite := by
  have coords_inj : Function.Injective targetCoords := by
    rintro (_ | ⟨x,y,h⟩) (_ | ⟨x',y',h'⟩) eqn
    · rfl
    · contradiction
    · contradiction
    · simpa only [targetCoords, Option.some.injEq, Prod.mk.injEq, Point.some.injEq] using eqn
  cases P with
  | zero =>
    simpa only [show Point.zero = (0:E) from rfl, map_zero, Set.range_const] using Set.finite_singleton (0:E)
  | some x y h =>
    have conjugates (a : K) (σ : Gal) : σ a ∈ (minpoly ℚ a).rootSet K :=
      Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral a),
        minpoly.aeval_algHom ℚ σ.toAlgHom a⟩
    have fin := ((Polynomial.rootSet_finite (minpoly ℚ x) K).prod
      (Polynomial.rootSet_finite (minpoly ℚ y) K)).image Option.some
    refine Set.Finite.of_finite_image (f := targetCoords) (fin.subset ?_) coords_inj.injOn
    rintro _ ⟨_,⟨σ,rfl⟩,rfl⟩
    exact ⟨(σ x,σ y),⟨conjugates x σ,conjugates y σ⟩,(targetAction_coords σ x y h).symm⟩

/-- The quadratic character on the target point, with the chosen root of minus d. -/
def signedTarget (d : ℕ) (σ : Gal) (P : E) : E :=
  if σ (Rank.sqrtMinus d) = Rank.sqrtMinus d then P else -P

/-- Galois anti-invariance in the group of geometric points modulo torsion. -/
def MinusModuloTorsion (d : ℕ) (P : E) : Prop :=
  ∀ σ : Gal, IsOfFinAddOrder (targetAction σ P - signedTarget d σ P)

theorem finite_signed_differences (d : ℕ) (P : E) :
    (Set.range fun σ : Gal => targetAction σ P - signedTarget d σ P).Finite := by
  let orbit := Set.range fun σ : Gal => targetAction σ P
  have h : orbit.Finite := finite_target_orbit P
  apply ((h.image (fun Q => Q-P)).union (h.image (fun Q => Q-(-P)))).subset
  rintro _ ⟨σ,rfl⟩
  by_cases fixed : σ (Rank.sqrtMinus d) = Rank.sqrtMinus d
  · exact Or.inl ⟨_,⟨σ,rfl⟩,by simp [signedTarget,fixed]⟩
  · exact Or.inr ⟨_,⟨σ,rfl⟩,by simp [signedTarget,fixed]⟩

/-- A finite set of torsion elements has a common positive annihilator. -/
theorem finite_torsion_exponent {G : Type*} [AddCommGroup G] {T : Set G}
    (hT : T.Finite) (hord : ∀ P ∈ T, IsOfFinAddOrder P) :
    ∃ m : ℕ, 0 < m ∧ ∀ P ∈ T, m • P = 0 := by
  classical
  refine ⟨∏ Q ∈ hT.toFinset, addOrderOf Q,
    Finset.prod_pos (fun Q hQ => addOrderOf_pos_iff.mpr (hord Q (hT.mem_toFinset.mp hQ))), ?_⟩
  intro P hP
  obtain ⟨s,hs⟩ := Finset.dvd_prod_of_mem (fun Q : G => addOrderOf Q) (hT.mem_toFinset.mpr hP)
  rw [hs,mul_nsmul,addOrderOf_nsmul_eq_zero,nsmul_zero]

theorem minusModuloTorsion_iff (d : ℕ) (P : E) :
    MinusModuloTorsion d P ↔ ∃ m : ℕ, 0 < m ∧ GaloisMinus d (m • P) := by
  have ident (m : ℕ) (σ : Gal) : m • (targetAction σ P - signedTarget d σ P) =
      targetAction σ (m • P) - signedTarget d σ (m • P) := by
    unfold signedTarget
    split_ifs <;> simp [nsmul_sub, nsmul_add]
  constructor
  · intro H
    obtain ⟨m,hm,hkill⟩ := finite_torsion_exponent (finite_signed_differences d P)
      (fun Q ⟨σ,hσ⟩ => hσ ▸ H σ)
    refine ⟨m,hm,fun σ => ?_⟩
    exact sub_eq_zero.mp ((ident m σ).symm.trans (hkill _ ⟨σ,rfl⟩))
  · rintro ⟨m,hm,hanti⟩ σ
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m,hm,(ident m σ).trans (sub_eq_zero.mpr (hanti σ))⟩

/-- A non-torsion point anti-invariant modulo torsion gives the actual rational
abscissa and twisted rational ordinate required by the public rank theorem. -/
theorem antiPoint_of_minusModuloTorsion {n : ℕ} (hn : 0 < n) {P : E}
    (hinf : Rank.InfiniteOrder P) (hminus : MinusModuloTorsion n P) : Rank.AntiPoint n := by
  obtain ⟨m,hm,ha⟩ := (minusModuloTorsion_iff n P).mp hminus
  have hmi : Rank.InfiniteOrder (m • P) := by
    intro k hk hz
    exact hinf (m*k) (Nat.mul_pos hm hk) ((mul_nsmul _ _ _).trans hz)
  obtain hz | ⟨u,v,h,he⟩ := (minus_iff_coordinates hn _).mp ha
  · exact False.elim (hmi 1 (by decide) (by simpa using hz))
  · exact ⟨u,v,h,he ▸ hmi⟩

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.finite_target_orbit
#print axioms ZInQBlueprint.TYZ.Specialization.finite_signed_differences
#print axioms ZInQBlueprint.TYZ.Specialization.finite_torsion_exponent
#print axioms ZInQBlueprint.TYZ.Specialization.minusModuloTorsion_iff
#print axioms ZInQBlueprint.TYZ.Specialization.antiPoint_of_minusModuloTorsion
