import BranchParity
import IntegralInfinity

/-! Certificates on the actual chart coefficients for the contact and pole branches. -/
namespace SixContactFour
open Polynomial IsDiscreteValuationRing
open ZInQBlueprint.ResidueExtension ZInQBlueprint.PrimitiveParameters ZInQBlueprint.ClusterRoots
open ZInQBlueprint.ClusterPicture ZInQBlueprint.LeadingOrders ZInQBlueprint.RationalClusters
open ZInQBlueprint.RationalReduction ZInQBlueprint.DirectCharts ZInQBlueprint.BinaryCover
noncomputable section

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

def transformed {f : W[X]} {s : W} (T : SexticFibre f s) (c : W) (i : Fin 5) : W :=
  oddRoot c (point T fixedBranch) (point T ∘ others) i

/-- Each individual difference has a square root in an explicitly finite étale algebra.
The input unit can be nonsquare over the residue field. -/
theorem etale_square {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (two : IsUnit (2:R)) {π x : R} (hπ : Irreducible π)
    {n : ℕ} (h : addVal R x=((2*n:ℕ):ℕ∞)) :
    ∃ u : Rˣ, Module.Finite R (Cover (u:R)) ∧ Algebra.Etale R (Cover (u:R)) ∧
      ∃ z : Cover (u:R), z^2=algebraMap R (Cover (u:R)) x := by
  obtain ⟨u,he⟩ := square_times_unit hπ h
  let w : Cover (u:R) := QuadraticAlgebra.omega
  have hw : w^2=algebraMap R (Cover (u:R)) (u:R) := by
    change (QuadraticAlgebra.omega : QuadraticAlgebra R (u:R) 0)^2=_
    rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap,map_zero,zero_mul,add_zero]
  refine ⟨u,inferInstance,ZInQBlueprint.OrdinaryModel.etale_quadratic u two,
    (algebraMap R (Cover (u:R)) π)^n*w,?_⟩
  rw [he,mul_pow,hw,map_mul,map_pow,map_pow]

private theorem chart_radicals {u : ℚ} {v a : Zpˣ} {t : Zp} {k l : ℕ}
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^k))
    (hc : addVal W (equation p u v a t).leadingCoeff=(l:ℕ∞))
    (he : Even (l+k)) (i j : Fin 5) (ij : i ≠ j) :
    ∃ n : ℕ, addVal W (transformed p T (equation p u v a t).leadingCoeff i -
      transformed p T (equation p u v a t).leadingCoeff j)=((2*n:ℕ):ℕ∞) := by
  apply all_even (point T) _ l k hc _ he i j ij
  intro x y xy
  rw [dvr_distances (uniformizer p) k T,ite_eq_right xy]
  split <;> rfl

def chartDifferences {f : W[X]} {s : W} (T : SexticFibre f s) (c : W) : Prop :=
  ∀ i j : Fin 5, i ≠ j → ∃ n : ℕ, addVal W (transformed p T c i-transformed p T c j)=((2*n:ℕ):ℕ∞)

/-- The actual even-contact chart with the single project-wide twist. -/
theorem even_contact_differences (u : ℚ) (hp : 17≤p) (k : ℕ) (hk : 0<k)
    (hf : addVal Zp (F p u)=((2*k:ℕ):ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^k),
        chartDifferences p T (equation p u v a t).leadingCoeff := by
  obtain ⟨t,v,a,H,T,hs⟩ := even_contact_chart p u hp k hk hf
  exact ⟨t,v,a,H,T,fun i j ij => chart_radicals p T hs.1 (by
    rw [Nat.even_iff]; omega) i j ij⟩

/-- The actual pole chart, allowing odd or even pole order. -/
theorem pole_differences (u : ℚ) (hp : 17≤p) (g : ℕ) (hg : 0<g)
    (hG : addVal Zp (G p u)=(g:ℕ∞)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p (t:Zp))) ((p:W)^g),
        chartDifferences p T (equation p u 1 a t).leadingCoeff := by
  obtain ⟨t,a,H,T,hs,_⟩ := pole_chart p u hp g hg hG
  exact ⟨t,a,H,T,fun i j ij => chart_radicals p T hs.1 ⟨g,rfl⟩ i j ij⟩

end
end SixContactFour
#print axioms SixContactFour.etale_square
#print axioms SixContactFour.even_contact_differences
#print axioms SixContactFour.pole_differences
