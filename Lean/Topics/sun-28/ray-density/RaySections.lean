import GaussianUnits
import DyadicRay
import RayEuler

namespace Sun28.RayDensity
open Finset Sun28.MixedSieve
noncomputable section

/-- The two actual adjacent norms are nonzero in the residue ring. -/
def admissible {p : ℕ} (z : GU p) : Prop :=
    ((1 : GR p)+(z:GR p)).norm ≠ 0 ∧ ((1 : GR p)-(z:GR p)).norm ≠ 0

def allowedFibre (p : ℕ) (t : (ZMod p)ˣ) := {z : normFibre p t // admissible z.1}
abbrev safeCircle (p : ℕ) [Fact p.Prime] (t : ZMod p) :=
    {z : Circle p t // z∉bad p t true ∪ bad p t false}

theorem adjacent_iff {p : ℕ} [Fact p.Prime] (t : (ZMod p)ˣ) (z : normFibre p t) :
    admissible z.1 ↔ (fibreCoords t z)∉bad p _ true ∪ bad p _ false := by
  classical
  let x := (z.1:GR p).re
  let y := (z.1:GR p).im
  have plus : ((1:GR p)+(z.1:GR p)).norm=(x+1)^2+y^2 := by
    simp [norm_coordinates,x,y,add_comm]
  have minus : ((1:GR p)-(z.1:GR p)).norm=(x+ -1)^2+y^2 := by
    simp [norm_coordinates,x,y];ring
  simp only [admissible,plus,minus,mem_union,not_or,bad,mem_filter,mem_univ,true_and,
      ite_true]
  rfl

def allowedCoords {p : ℕ} [Fact p.Prime] (t : (ZMod p)ˣ) : allowedFibre p t ≃ safeCircle p (t:ZMod p) :=
  Equiv.subtypeEquiv (fibreCoords t) (adjacent_iff t)

/-- Cardinal ratio of actual admissible units with the specified norm. -/
def survival (p : ℕ) (t : (ZMod p)ˣ) : ℝ := (Nat.card (allowedFibre p t):ℝ)/Nat.card (normFibre p t)

theorem survival_eq {p : ℕ} [Fact p.Prime] (t : (ZMod p)ˣ) :
    survival p t = (((bad p (t:ZMod p) true ∪ bad p (t:ZMod p) false)ᶜ.card : ℝ) /
        Fintype.card (Circle p (t:ZMod p))) := by
  classical
  rw [survival,Nat.card_congr (allowedCoords t),Nat.card_congr (fibreCoords t)]
  let S := bad p (t:ZMod p) true ∪ bad p (t:ZMod p) false
  have e : safeCircle p (t:ZMod p) ≃ ↥(Sᶜ) :=
    Equiv.subtypeEquiv (Equiv.refl _) fun z => (Finset.mem_compl (s:=S) (a:=z)).symm
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem survival_lower {p : ℕ} [Fact p.Prime] (hp : 7≤p) (t : (ZMod p)ˣ) :
    both p ≤ survival p t := by
  rw [survival_eq]
  exact Sun28.FinitePattern.paper_fibre hp t.ne_zero

/-- The prescribed rational norm class at 3 and 5 has four lifts, two admissible. -/
theorem small_fibres :
    survival 3 1=1/2 ∧ survival 5 1=1/2 := by
  let _ : Fact (3:ℕ).Prime := ⟨by decide⟩
  let _ : Fact (5:ℕ).Prime := ⟨by decide⟩
  have c3 : Fintype.card (Circle 3 1)=4 := by decide
  have c5 : Fintype.card (Circle 5 1)=4 := by decide
  have s3 : ((bad 3 1 true ∪ bad 3 1 false)ᶜ).card=2 := by decide
  have s5 : ((bad 5 1 true ∪ bad 5 1 false)ᶜ).card=2 := by decide
  simp only [survival_eq,Units.val_one,s3,s5,c3,c5];norm_num

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.adjacent_iff
#print axioms Sun28.RayDensity.allowedCoords
#print axioms Sun28.RayDensity.survival_eq
#print axioms Sun28.RayDensity.small_fibres
#print axioms Sun28.RayDensity.survival_lower
