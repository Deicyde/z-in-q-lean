import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-! The finite wild subgroup of a rank-two representation over a field. -/
namespace ZInQBlueprint.WildLevel
open Matrix
open scoped MatrixGroups
noncomputable section
variable {K : Type*} [Field K]

abbrev projectivize (H : Subgroup (GL (Fin 2) K)) :=
  (ProjGenLinGroup.mk (n:=Fin 2) (R:=K)).comp H.subtype

private theorem scalar_of_kernel (H : Subgroup (GL (Fin 2) K)) (x : (projectivize H).ker) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin 2) u=x.val.val := by
  have h : ProjGenLinGroup.mk x.val.val = 1 := x.property
  have c := ProjGenLinGroup.mk_eq_one.mp h
  rw [GeneralLinearGroup.center_eq_range_scalar] at c
  exact c

/-- A scalar in a binary representation with determinant of exponent d
is a (2d)-th root of unity. This bounds the entire projective kernel. -/
theorem scalar_kernel_bound (H : Subgroup (GL (Fin 2) K)) (d : ℕ) (hd : 0<d)
    (detOrder : ∀ x:H, x.val.det^d=1) :
    Nat.card (projectivize H).ker ≤ 2*d := by
  classical
  let _ : NeZero (2*d) := ⟨by positivity⟩
  let scalar (x : (projectivize H).ker) := (scalar_of_kernel H x).choose
  have repr (x : (projectivize H).ker) : GeneralLinearGroup.scalar (Fin 2) (scalar x)=x.val.val :=
    (scalar_of_kernel H x).choose_spec
  have root (x : (projectivize H).ker) : scalar x ∈ rootsOfUnity (2*d) K := by
    have h := detOrder x.val
    rw [←repr x, GeneralLinearGroup.det_scalar, Fintype.card_fin, ←pow_mul] at h
    exact (mem_rootsOfUnity _ _).mpr h
  let embed (x : (projectivize H).ker) : rootsOfUnity (2*d) K := ⟨scalar x,root x⟩
  have inj : Function.Injective embed := by
    intro x y eq
    have equal : scalar x=scalar y := congrArg Subtype.val eq
    exact Subtype.ext (Subtype.ext ((repr x).symm.trans ((congrArg _ equal).trans (repr y))))
  exact (Nat.card_le_card_of_injective embed inj).trans (card_rootsOfUnity ..)

theorem wild_card_bound (H : Subgroup (GL (Fin 2) K)) [Finite H] (d : ℕ) (hd : 0<d)
    (detOrder : ∀ x:H, x.val.det^d=1) :
    Nat.card H ≤ Nat.card (projectivize H).range*(2*d) := by
  calc Nat.card H = Nat.card (H ⧸ (projectivize H).ker)*Nat.card (projectivize H).ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
       _ = Nat.card (projectivize H).range*Nat.card (projectivize H).ker := by
         rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
       _ ≤ _ := Nat.mul_le_mul_left _ (scalar_kernel_bound H d hd detOrder)

/-- The order of the projective dyadic image divides twelve at the auxiliary
prime five. Its odd factor disappears before reinstating the scalars. -/
theorem dyadic_image (H : Subgroup (GL (Fin 2) K)) [Finite H] (wild : IsPGroup 2 H)
    (residue : Nat.card (projectivize H).range ∣ 12) (detOrder : ∀ x:H, x.val.det^2=1) :
    Nat.card H ≤ 16 := by
  let _ : Finite (projectivize H).range := Finite.of_surjective _ (projectivize H).rangeRestrict_surjective
  have img := wild.of_surjective (projectivize H).rangeRestrict (projectivize H).rangeRestrict_surjective
  obtain ⟨n, hn⟩ := img.exists_card_eq
  have cop : (Nat.card (projectivize H).range).Coprime 3 := by
    rw [hn]; exact (by decide : Nat.Coprime 2 3).pow_left n
  have small : Nat.card (projectivize H).range ∣ 4 :=
    cop.dvd_of_dvd_mul_left (by simpa only [show 3*4=12 by decide] using residue)
  exact (wild_card_bound H 2 (by decide) detOrder).trans
    (Nat.mul_le_mul_right 4 (Nat.le_of_dvd (by decide) small))

/-- At odd p use a quaternion residue quotient of order coprime to p. The
projective image vanishes and determinant one kills the scalar kernel. -/
theorem odd_image (H : Subgroup (GL (Fin 2) K)) [Finite H] {p q : ℕ} [Fact p.Prime]
    (wild : IsPGroup p H) (odd : p.Coprime 2) (cop : p.Coprime q)
    (residue : Nat.card (projectivize H).range ∣ q) (detOrder : ∀ x:H, x.val.det=1) :
    Nat.card H=1 := by
  let _ : Finite (projectivize H).range := Finite.of_surjective _ (projectivize H).rangeRestrict_surjective
  have img := wild.of_surjective (projectivize H).rangeRestrict (projectivize H).rangeRestrict_surjective
  obtain ⟨n, hn⟩ := img.exists_card_eq
  have proj : Nat.card (projectivize H).range=1 := by
    rw [hn] at residue ⊢
    exact Nat.eq_one_of_dvd_coprimes (cop.pow_left n) dvd_rfl residue
  have bound := wild_card_bound H 1 (by decide) (fun x => by simpa using detOrder x)
  rw [proj] at bound
  obtain ⟨k,hk⟩ := wild.exists_card_eq
  have pos := Nat.card_pos (α:=H)
  have co : (Nat.card H).Coprime 2 := hk ▸ odd.pow_left k
  interval_cases h : Nat.card H <;> simp_all

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.scalar_kernel_bound
#print axioms ZInQBlueprint.WildLevel.wild_card_bound
#print axioms ZInQBlueprint.WildLevel.dyadic_image
#print axioms ZInQBlueprint.WildLevel.odd_image
