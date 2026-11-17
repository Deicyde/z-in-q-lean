import DyadicRay
import Mathlib.Tactic

set_option maxRecDepth 50000
set_option maxHeartbeats 12000000

namespace Sun28.RayDensity.Artin
open Finset

def times {m : ℕ} (z w : Pair m) : Pair m :=
  (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)

def norm32 (z : Pair 16) : ZMod 32 := (z.1.val:ZMod 32)^2+(z.2.val:ZMod 32)^2

def inverse16 (z : Pair 16) : Pair 16 :=
  (z.1*(pairNorm z)^3,-z.2*(pairNorm z)^3)

theorem primary_operations :
    (1,0) ∈ primarySet ∧ (∀ a∈primarySet, conjPair a ∈ primarySet) ∧
    (∀ a∈primarySet, inverse16 a ∈ primarySet ∧ times (inverse16 a) a = (1,0)) ∧
    (∀ a∈primarySet, ∀ b∈primarySet, times a b ∈ primarySet) := by decide

/-- Norm characters and coboundaries in the actual dyadic component. -/
theorem dyadic_tables :
    primarySet.image norm32 = univ.filter (fun r:ZMod 32=>r.val % 4=1) ∧
    primarySet.image (ratioPair 3) = primarySet.filter (fun z=>norm32 z=1) ∧
    (∀ a∈primarySet, norm32 (conjPair a)=norm32 a ∧ (norm32 a)^8=1) ∧
    (∀ a∈primarySet, times a (inverse16 (conjPair a))=ratioPair 3 a) := by decide

theorem even_square_lift : ∀ s:ZMod 32,
    (((ZMod.castHom (by decide : 16∣32) (ZMod 16) s).val:ℕ):ZMod 32)^2=s^2 := by decide

/-- Ordinary integral norms give the lifted dyadic character, including signed representatives. -/
theorem norm32_integer (a b:ℤ) :
    norm32 ((a:ZMod 16),(b:ZMod 16))=((a^2+b^2:ℤ):ZMod 32) := by
  have H (x:ℤ) : ((((x:ZMod 16).val:ℕ):ZMod 32)^2) = (x:ZMod 32)^2 := by
    simpa only [map_intCast] using even_square_lift (x:ZMod 32)
  simp only [norm32,Int.cast_add,Int.cast_pow,H]

/-- Multiplication is inherited from Gaussian integer multiplication; the lift
is multiplicative on all residues, before restriction to primary elements. -/
theorem norm32_times (a b:Pair 16) : norm32 (times a b) = norm32 a * norm32 b := by
  obtain ⟨x,y⟩:=a
  obtain ⟨s,t⟩:=b
  let X:ℤ:=x.val
  let Y:ℤ:=y.val
  let S:ℤ:=s.val
  let T:ℤ:=t.val
  have xs : (X:ZMod 16)=x := by simp [X]
  have ys : (Y:ZMod 16)=y := by simp [Y]
  have ss : (S:ZMod 16)=s := by simp [S]
  have ts : (T:ZMod 16)=t := by simp [T]
  have E : times (x,y) (s,t) = (((X*S-Y*T:ℤ):ZMod 16),((X*T+Y*S:ℤ):ZMod 16)) := by
    simp [times,xs,ys,ss,ts]
  rw [E,norm32_integer,←xs,←ys,←ss,←ts,norm32_integer,norm32_integer]
  push_cast
  ring

theorem base_coset_is_norm_fibre :
    cmCoset 3 primarySet (9,0) = primarySet.filter (fun z=>norm32 z=17) ∧
    cmCoset 5 sevenUnits (1,3) = sevenUnits.filter (fun z=>pairNorm z=3) := by decide

end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.primary_operations
#print axioms Sun28.RayDensity.Artin.dyadic_tables
#print axioms Sun28.RayDensity.Artin.even_square_lift
#print axioms Sun28.RayDensity.Artin.norm32_integer
#print axioms Sun28.RayDensity.Artin.norm32_times
#print axioms Sun28.RayDensity.Artin.base_coset_is_norm_fibre
