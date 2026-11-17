import GaussianUnits
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SemidirectProduct

namespace Sun28.RayDensity
open SemidirectProduct
open scoped commutatorElement
noncomputable section

abbrev C₂ := Multiplicative (ZMod 2)
def flip : C₂ := Multiplicative.ofAdd (1:ZMod 2)

theorem two_cases (c : C₂) : c=1 ∨ c=flip := by
  have all : ∀ u : ZMod 2,u=0 ∨ u=1 := by decide
  exact all c.toAdd

variable {A : Type*} [CommGroup A]

def act (s : MulAut A) (involution : s*s=1) : C₂ →* MulAut A where
  toFun c := if c=1 then 1 else s
  map_one' := by simp
  map_mul' c d := by
    have ne : flip≠1 := by decide
    have ff : flip*flip=1 := by decide
    rcases two_cases c with rfl|rfl <;> rcases two_cases d with rfl|rfl <;>
      simp [ne,ff,involution]

def delta (s : MulAut A) : A →* A := (MonoidHom.id _)/s.toMonoidHom

/-- The derived group of an abelian group extended by an involution consists precisely
of its conjugation quotients. No restriction-map or Galois-group conditions occur. -/
theorem semidirect_derived (s : MulAut A) (h : s*s=1) :
    commutator (SemidirectProduct A C₂ (act s h)) =
      (delta s).range.map (SemidirectProduct.inl (φ:=act s h)) := by
  let H:=(delta s).range
  let Q:=QuotientGroup.mk' H
  have fixed (c : C₂) (a : A) : Q (act s h c a)=Q a := by
    rcases two_cases c with rfl|rfl
    · simp
    · change Q ((if flip=1 then (1:MulAut A) else s) a)=Q a
      rw [ite_eq_right (by decide : flip≠1)]
      symm
      apply QuotientGroup.eq_iff_div_mem.mpr
      exact ⟨a,rfl⟩
  let F : SemidirectProduct A C₂ (act s h) →* (A ⧸ H) × C₂ :=
    { toFun := fun v=>(Q v.left,v.right)
      map_one' := by simp
      map_mul' := fun a b=> by apply Prod.ext <;> simp [fixed] }
  have K : F.ker = H.map (inl (φ:=act s h)) := by
    ext x
    constructor
    · intro hx
      have e : (Q x.left,x.right) = (1,1) := hx
      have a : x.left∈H := (QuotientGroup.eq_one_iff _).mp (congrArg Prod.fst e)
      have b : x.right=1 := congrArg Prod.snd e
      exact ⟨x.left,a, by apply SemidirectProduct.ext <;> simp [b]⟩
    · rintro ⟨a,ha,rfl⟩
      exact Prod.ext ((QuotientGroup.eq_one_iff a).mpr ha) rfl
  apply le_antisymm
  · rw [←K,commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change F ⁅x,y⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rintro x ⟨a,⟨b,rfl⟩,rfl⟩
    let c : SemidirectProduct A C₂ (act s h) := inr flip
    have e : (inl (φ:=act s h)) (s b) = c*inl b*c⁻¹ := by
      have lead:=inl_aut (φ:=act s h) flip b
      have inv : (inr (φ:=act s h)) flip⁻¹ = ((inr (φ:=act s h)) flip)⁻¹ := map_inv _ _
      rw [inv] at lead
      have acted : (act s h flip) b=s b := by
        change (if flip=1 then (1:MulAut A) else s) b = s b
        rw [ite_eq_right (by decide : flip≠1)]
      rw [acted] at lead
      exact lead
    have eq : (inl (φ:=act s h)) (delta s b)=⁅(inl (φ:=act s h)) b,c⁆ := by
      change (inl (φ:=act s h)) (b/s b)=_
      rw [map_div,e,commutatorElement_def,div_eq_mul_inv]
      group
    rw [eq]
    exact Subgroup.commutator_mem_commutator (by trivial : inl (φ:=act s h) b∈(⊤ : Subgroup _))
      (by trivial : c∈(⊤ : Subgroup _))

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.two_cases
#print axioms Sun28.RayDensity.semidirect_derived
