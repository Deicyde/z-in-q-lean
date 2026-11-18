module

public import Std

@[expose] public section

namespace AbscissaRatio
open Lean.Grind

theorem linear_factors {R : Type} [CommRing R] (c z : R) :
    (c-1)*(c+3)*(z+3) + 3*(c-1)^2*(z-1) = 4*(c-1)*(c*z+3) ∧
    (c-1)*(c+3)*(z+3) + (3*c+1)*(c+3)*(z-1) = 4*(c+3)*(c*z-1) := by
  constructor <;> grobner

theorem section_point {R : Type} [CommRing R] (c : R) :
    let a := 3*(c-1)^2
    let b := (3*c+1)*(c+3)
    let d := (c-1)*(c+3)
    d*(d+a)*(d+b) = (4*c*d)^2 := by
  dsimp; grobner

theorem double_numerator {R : Type} [CommRing R] (c : R) :
    let a := 3*(c-1)^2
    let b := (3*c+1)*(c+3)
    let d := (c-1)*(c+3)
    d^2-a*b = -8*c*d*(c-1) := by
  dsimp; grobner

theorem fourth_numerator {R : Type} [CommRing R] (c : R) :
    (c-1)^4-3*(c-1)^2*((3*c+1)*(c+3)) = -8*(c-1)^2*(c^2+4*c+1) ∧
    (c-1)^2*((c-1)^2+3*(c-1)^2)*((c-1)^2+(3*c+1)*(c+3))
      = (4*(c-1)^2*(c+1))^2 := by
  constructor <;> grobner

theorem integral_numerator {R : Type} [CommRing R] (u v : R) :
    u^2+4*u*v+v^2 = (u+v)^2+2*u*v := by grobner

theorem pencil_discriminant {R : Type} [CommRing R] (s t c : R) :
    -3*(s+c^2*t)*(s+t)-(s+c*t)^2 =
      -(4*s^2+(3*c^2+2*c+3)*s*t+4*c^2*t^2) := by grobner

theorem conic_character {R : Type} [CommRing R] (d a b : R) :
    let h := b^2+3*d*a^2
    let k := b^2-d*a^2
    h*(h+3*k) = 4*b^2*h ∧ (h-k)*(h+3*k)=d*(4*a*b)^2 := by
  dsimp; constructor <;> grobner

set_option exponentiation.threshold 640 in
/-- The normalized tangent unit at the surviving ratio. -/
theorem last_unit : (1165 : Nat)^638 % 1277 = 1276 := by decide

def negativeUnit (p q : Nat) : Bool :=
  ((if p = q then 1 else q) ^ ((p-1)/2)) % p != 1

/-- Prime factors on which the two unit characters differ. -/
theorem character_support :
    ([2,3,5,7,11,13,17,131,269,317,457,487,1277,2819,59929,233026789,
      27146050171,322269869512007] : List Nat).filter
        (fun q => negativeUnit 5 q != negativeUnit 317 q) =
      [5,7,269,317,1277,322269869512007] := by decide

/-- Counting directions that satisfy at least one or both residue tests. -/
theorem count_union_inter {α : Type} (xs : List α) (f g : α → Bool) :
    xs.countP (fun x => f x || g x) + xs.countP (fun x => f x && g x) =
      xs.countP f + xs.countP g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hf : f a <;> cases hg : g a <;>
      simp [hf, hg] <;> omega

theorem two_common_directions {α : Type} (xs : List α) (f g : α → Bool) (q : Nat)
    (hsize : xs.length = q+1) (hcount : xs.countP f + xs.countP g = q+3) :
    2 ≤ xs.countP (fun x => f x && g x) := by
  have h := count_union_inter xs f g
  have hle := List.countP_le_length (l := xs) (p := fun x => f x || g x)
  omega

#print axioms count_union_inter
#print axioms two_common_directions
#print axioms last_unit
#print axioms character_support
#print axioms linear_factors
#print axioms section_point
#print axioms double_numerator
#print axioms fourth_numerator
#print axioms integral_numerator
#print axioms pencil_discriminant
#print axioms conic_character
end AbscissaRatio
