import Std
namespace NormPencil
open Lean.Grind

theorem involution {R : Type} [CommRing R] (β l a b : R) :
    let u := b-β*l*a
    let v := β*(3*a+l*b)
    let h := β*(3+β*l^2)
    v-β*l*u=h*a ∧ β*(3*u+l*v)=h*b := by
  dsimp
  constructor <;> grobner

theorem pencil_similitudes {R : Type} [CommRing R] (β l a b : R) :
    let u := b-β*l*a
    let v := β*(3*a+l*b)
    let h := β*(3+β*l^2)
    v^2+3*β*u^2=h*(b^2+3*β*a^2) ∧
    (v+β*l*u)^2+3*β*(u+l*v)^2=h*((b+β*l*a)^2+3*β*(a+l*b)^2) := by
  dsimp
  constructor <;> grobner

theorem exterior_difference {R : Type} [CommRing R] (s l : R) :
    (3*s+l)^2-(1-l*s)^2=(1-l^2)*(s^2-1)+8*s*(s+l) := by grobner

theorem prescribed_second {R : Type} [CommRing R] (θ a b : R) :
    let d := a^2+3*θ*b^2
    let g := (a^2-θ*b^2)*(a^2-9*θ*b^2)
    d^2-g=θ*(4*a*b)^2 ∧ d^2+3*g=(2*(a^2-3*θ*b^2))^2 := by
  dsimp
  constructor <;> grobner

theorem displayed_norms :
    let β : Int := 428100015625821236629910708274545
    β*12^2+59929*677231147437751^2=298550431736060597^2 ∧
    β*12^2+59929*867330881093879^2=326693683785277813^2 := by decide

/-- Valuations of the revised, shared-norm-preserving scalar rows. -/
theorem reciprocal_depth (η α γ u v : Int)
    (hp : 1 ≤ η) (hb : 33*η < 2*α)
    (hq : 33*η < 2*(η+2*γ-α))
    (hu : α+16*η ≤ 2*u) (hv : α+17*η ≤ 2*v) :
    17 ≤ u ∧ 17 ≤ v ∧ 16*η < γ := by omega

theorem reference_depth (η c e : Int) (hr : 0 ≤ η) (hc : 0 ≤ c)
    (he : 17*η+c+2 ≤ e) : 8 ≤ 4*e-65*η-c := by omega

#print axioms reciprocal_depth
#print axioms reference_depth
#print axioms involution
#print axioms pencil_similitudes
#print axioms exterior_difference
#print axioms prescribed_second
#print axioms displayed_norms
end NormPencil
