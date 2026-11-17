import SmallMarkedImage
import ZInQKernel.RouteK.Selmer.PadicSquare

namespace Sun28.SeededPartners
open Sun28.SelmerRealization ZInQ.RouteK.Selmer

/-- Rescale only the last homogeneous coordinate when changing the twist by a square. -/
theorem local_twist_transport {K : Type*} [Field K] [CharZero K] {m l : ℕ} {a b : ℤ}
    {u : K} (un : u≠0) (eq : (l:K)=(m:K)*u^2) (h : Cover K l a b) : Cover K m a b := by
  obtain ⟨X,Y,Z,T,N,E,F⟩:=h
  refine ⟨X,Y,Z,u*T,?_,?_,?_⟩
  · rcases N with H|H|H|H
    · exact Or.inl H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr (Or.inl H))
    · exact Or.inr (Or.inr (Or.inr (mul_ne_zero un H)))
  · rw [eq] at E;linear_combination E
  · rw [eq] at F;linear_combination F

/-- Locally square-equivalent twists have the same soluble ordered labels. -/
theorem scale_curve {K : Type*} [Field K] [CharZero K] {l m : ℕ} {a b : ℤ}
    {u : K} (un : u≠0) (eq : (l:K)=(m:K)*u^2) :
    Cover K l a b ↔ Cover K m a b := by
  refine ⟨local_twist_transport un eq,local_twist_transport (inv_ne_zero un) ?_⟩
  rw [eq];field_simp

/-- A square quotient of the twist parameters gives an isomorphism of these two covers. -/
theorem cover_of_square_quotient {K : Type*} [Field K] [CharZero K] {l m : ℕ} {a b : ℤ}
    (lp : 0<l) (mp : 0 < m) (s : IsSquare ((l:K)/(m:K))) (H : Cover K l a b) : Cover K m a b := by
  have lm : (l:K) ≠ 0 := Nat.cast_ne_zero.mpr lp.ne'
  have mm : (m:K) ≠ 0 := Nat.cast_ne_zero.mpr mp.ne'
  obtain ⟨u,eq⟩:=s
  have un : u≠0 := by
    intro h
    rw [h,zero_mul] at eq
    exact (div_ne_zero lm mm) eq
  have eqL : (l:K)=(m:K)*u^2 := by
    calc
      _ = (u*u)*(m:K) := (div_eq_iff mm).mp eq
      _ = _ := by ring
  exact local_twist_transport (m:=m) (l:=l) (a:=a) (b:=b) un eqL H

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.scale_curve
