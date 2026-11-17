import QuadraticPivots

namespace OrbitIdentification
open Lean.Grind

abbrev Pair := Rat × Rat
def times (x y : Pair) : Pair := (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)
def sq (x : Pair) := times x x
def norm (x : Pair) := x.1^2-2*x.2^2

def representative (neg delta eps : Bool) : Pair :=
  times (if neg then (-1,0) else (1,0))
    (times (if delta then (3,-1) else (1,0)) (if eps then (1,1) else (1,0)))

private theorem sq_nonnegative (q : Rat) : 0≤q*q := by
  rcases Rat.nonneg_total q with hp|hn
  · exact Rat.mul_nonneg hp hp
  · have h:=Rat.mul_nonneg hn hn
    rwa [show -q*(-q)=q*q by grobner] at h

theorem norm_sq (q : Pair) : norm (sq q)=(norm q)^2 := by
  dsimp [norm,sq,times]
  grobner

private theorem nonnegative (q : Rat) : 0≤q^2 := by
  have h:=sq_nonnegative q
  rwa [show q*q=q^2 by grobner] at h

private theorem negative_norm (q x : Rat) (h : q^2=x) (neg : x<0) : False := by
  have hp:=nonnegative q
  grind

private theorem minus_one (q : Pair) : sq q≠(-1,0) := by
  intro eq
  have h:=congrArg Prod.fst eq
  change q.1*q.1+2*q.2*q.2= -1 at h
  have h1:=sq_nonnegative q.1
  have h2:=sq_nonnegative q.2
  grind

/-- All seven nonidentity squareclasses on the marked curve are detected by
    a rational norm, except for minus one, excluded by its first coefficient. -/
theorem square_representative (a d e : Bool) (z : Pair)
    (rep : sq z=representative a d e) : a=false ∧ d=false ∧ e=false := by
  have n := (norm_sq z).symm.trans (congrArg norm rep)
  have seven := CircuitTransport.Quadratic.no_square_in_gap (n:=7) (k:=2)
    (by decide) (by decide) (norm z)
  cases a <;> cases d <;> cases e
  · exact ⟨rfl,rfl,rfl⟩
  · exact False.elim (negative_norm _ (-1) (n.trans (by decide +kernel)) (by decide))
  · exact False.elim (seven (n.trans (by decide +kernel)))
  · exact False.elim (negative_norm _ (-7) (n.trans (by decide +kernel)) (by decide))
  · exact False.elim (minus_one z (rep.trans (by decide +kernel)))
  · exact False.elim (negative_norm _ (-1) (n.trans (by decide +kernel)) (by decide))
  · exact False.elim (seven (n.trans (by decide +kernel)))
  · exact False.elim (negative_norm _ (-7) (n.trans (by decide +kernel)) (by decide))

/-- A nonzero square abscissa has a unique free and torsion parity in the
    announced Mordell--Weil decomposition, whatever representative is used. -/
theorem class_of_square (a d e : Bool) (h s : Pair) (w : norm s≠0)
    (hs : sq h=times (representative a d e) (sq s)) :
    a=false ∧ d=false ∧ e=false := by
  let k:=representative a d e
  let M:=norm s
  let u:Pair:=((h.1*s.1-2*h.2*s.2)*M⁻¹,(h.2*s.1-h.1*s.2)*M⁻¹)
  have he : (sq h).1=(times k (sq s)).1 := congrArg Prod.fst hs
  have hf : (sq h).2=(times k (sq s)).2 := congrArg Prod.snd hs
  have i : M*M⁻¹=1 := Rat.mul_inv_cancel M w
  apply square_representative a d e u
  apply Prod.ext
  · have id : (h.1*s.1-2*h.2*s.2)^2+2*(h.2*s.1-h.1*s.2)^2=k.1*M^2 := by
      dsimp [times,sq] at he hf
      dsimp [M,norm]
      grobner
    change (u.1*u.1+2*u.2*u.2)=k.1
    calc _ = ((h.1*s.1-2*h.2*s.2)^2+2*(h.2*s.1-h.1*s.2)^2)*(M⁻¹)^2 := by dsimp [u]; grobner
         _ = _ := by rw [id]; grobner
  · have id : 2*(h.1*s.1-2*h.2*s.2)*(h.2*s.1-h.1*s.2)=k.2*M^2 := by
      dsimp [times,sq] at he hf
      dsimp [M,norm]
      grobner
    change u.1*u.2+u.2*u.1=k.2
    calc _ = (2*(h.1*s.1-2*h.2*s.2)*(h.2*s.1-h.1*s.2))*(M⁻¹)^2 := by dsimp [u]; grobner
         _ = _ := by rw [id]; grobner

/-- From the signed squareclass and ordinary group-coordinate statements
    for a point, obtain its actual integral multiple of the doubled generator. -/
theorem square_point_is_multiple {G : Type} [IntModule G] (Q R T U : G)
    (k : Int) (a d e : Bool) (h s : Pair) (w : norm s≠0)
    (coset : sq h=times (representative a d e) (sq s))
    (decomposition : Q=(2*k+(if e then 1 else 0)) • R +
      (if a then T else 0) + (if d then U else 0)) :
    Q=k • ((2:Int) • R) := by
  obtain ⟨rfl,rfl,rfl⟩ := class_of_square a d e h s w coset
  rw [decomposition]
  simp [IntModule.mul_zsmul,Int.mul_comm,AddCommMonoid.add_zero]
end OrbitIdentification

#print axioms OrbitIdentification.norm_sq
#print axioms OrbitIdentification.square_representative
#print axioms OrbitIdentification.class_of_square
#print axioms OrbitIdentification.square_point_is_multiple
