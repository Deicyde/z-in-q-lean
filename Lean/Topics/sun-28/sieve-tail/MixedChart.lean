import PrimeFibre
import AnalyticInputs

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection Sun28.MixedSieve Sun28.NormSieve

variable {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}

/-- Opposite adjacent orders are normalized to two positive translations by reflecting
only the real coordinate of the second Gaussian integer. -/
def tcoord (g h : Gaussian) : ℤ := g.1 + h.1
def xcoord (g h : Gaussian) : ℤ := g.2 - h.2
def zcoord (g h : Gaussian) : ℤ := g.2 + h.2
noncomputable def gap (i j : ↥(shifts A)) : ℤ :=
  offset (dilation A) i.val - offset (dilation A) j.val

private theorem norm_cast (g : Gaussian) : (gaussianNorm g : ℤ) = g.1^2+g.2^2 :=
  Int.natAbs_of_nonneg (by positivity)

theorem norm_gap (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    (gaussianNorm (a.gaussian i):ℤ) - gaussianNorm (a.gaussian j) = gap i j*(a.v:ℤ)^2 := by
  rw [a.rays.norm i, a.rays.norm j, a.values.equation i.val i.property,
    a.values.equation j.val j.property]
  unfold gap
  ring

theorem gap_ne_zero {i j : ↥(shifts A)} (ij : i ≠ j) : gap i j ≠ 0 := by
  intro h
  exact ij (Subtype.ext (offset_injective i.property j.property (sub_eq_zero.mp h)))

theorem hyperbolic (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    let g := a.gaussian i
    let h := a.gaussian j
    tcoord g h * (g.1-h.1) = gap i j*(a.v:ℤ)^2 - xcoord g h*zcoord g h := by
  dsimp only
  have e := norm_gap a i j
  rw [norm_cast,norm_cast] at e
  unfold tcoord xcoord zcoord
  linear_combination e

theorem order_difference (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    (adjacentNorm (a.gaussian i) true : ℤ) - adjacentNorm (a.gaussian j) false =
      gap i j*(a.v:ℤ)^2 + 2*tcoord (a.gaussian i) (a.gaussian j) := by
  have e := norm_gap a i j
  rw [norm_cast,norm_cast] at e
  simp only [adjacentNorm,ite_true,ite_false,Bool.false_eq_true, norm_cast, tcoord]
  linear_combination e

/-- The dyadic ray rules out the integer equality of a plus and a minus order,
even when a pair of distinct Gaussian primes has been chosen. -/
theorem ray_order_difference_ne_zero (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    gap i j*(a.v:ℤ)^2 + 2*tcoord (a.gaussian i) (a.gaussian j) ≠ 0 := by
  rw [←order_difference]
  have ai := (a.rays.ray16 i).1
  have bi := (a.rays.ray16 i).2
  have aj := (a.rays.ray16 j).1
  have bj := (a.rays.ray16 j).2
  change (a.gaussian i).1 % 16 = 9 at ai
  change (a.gaussian i).2 % 16 = 0 at bi
  change (a.gaussian j).1 % 16 = 9 at aj
  change (a.gaussian j).2 % 16 = 0 at bj
  have hcast (s : ℤ) (k : ℤ) (h : s % 16 = k % 16) : (s : ZMod 16) = (k : ZMod 16) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  have am := hcast _ 9 ai
  have bm := hcast _ 0 bi
  have an := hcast _ 9 aj
  have bn := hcast _ 0 bj
  intro zero
  have e := congrArg (fun n : ℤ => (n:ZMod 16)) zero
  simp only [adjacentNorm,ite_true,ite_false, Bool.false_eq_true, norm_cast] at e
  push_cast at e
  rw [am,bm,an,bn] at e
  norm_num at e
  exact (by decide : (36:ZMod 16) ≠ 0) e

theorem chart_product_identity (t x z k v : ℤ) :
    (k*v^2 - x*z+t^2+2*t)^2+t^2*(x+z)^2 -
      (t^2+x^2)*(t^2+z^2) =
    (k*v^2+2*t)*(k*v^2+2*t+2*t^2-2*x*z) := by ring

theorem mixed_chart {p : ℕ} [Fact p.Prime] (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (plus : p ∣ adjacentNorm (a.gaussian i) true)
    (minus : p ∣ adjacentNorm (a.gaussian j) false) :
    let g := a.gaussian i
    let h := a.gaussian j
    let t := tcoord g h
    let x := xcoord g h
    let z := zcoord g h
    (p:ℤ) ∣ gap i j*(a.v:ℤ)^2+2*t ∧
    ((p:ℤ) ∣ t^2+x^2 ∨ (p:ℤ) ∣ t^2+z^2) := by
  dsimp only
  have hp := Int.natCast_dvd_natCast.mpr plus
  have hm := Int.natCast_dvd_natCast.mpr minus
  have hd := dvd_sub hp hm
  rw [order_difference] at hd
  refine ⟨hd,?_⟩
  let t := tcoord (a.gaussian i) (a.gaussian j)
  let x := xcoord (a.gaussian i) (a.gaussian j)
  let z := zcoord (a.gaussian i) (a.gaussian j)
  have scalar : 4*t^2*(adjacentNorm (a.gaussian i) true:ℤ) =
      (gap i j*(a.v:ℤ)^2-x*z+t^2+2*t)^2+t^2*(x+z)^2 := by
    rw [←show t*((a.gaussian i).1-(a.gaussian j).1)=gap i j*(a.v:ℤ)^2-x*z from hyperbolic a i j]
    simp only [t,x,z,tcoord,xcoord,zcoord,adjacentNorm,ite_true,norm_cast]
    ring
  have vanish : (p:ℤ) ∣ (gap i j*(a.v:ℤ)^2-x*z+t^2+2*t)^2+t^2*(x+z)^2 :=
    scalar ▸ dvd_mul_of_dvd_right hp _
  have both : (p:ℤ) ∣ (t^2+x^2)*(t^2+z^2) := by
    have dp := dvd_mul_of_dvd_left hd (gap i j*(a.v:ℤ)^2+2*t+2*t^2-2*x*z)
    rw [←chart_product_identity] at dp
    exact (dvd_sub_right vanish).mp dp
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_mul.mp both

theorem divisor_or_single_chart {p : ℕ} [Fact p.Prime] (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (away : ¬(p:ℤ) ∣ gap i j)
    (plus : p ∣ adjacentNorm (a.gaussian i) true)
    (minus : p ∣ adjacentNorm (a.gaussian j) false) :
    p ∣ a.v ∨
      (¬(p:ℤ) ∣ tcoord (a.gaussian i) (a.gaussian j)) ∧
      (p:ℤ) ∣ gap i j*(a.v:ℤ)^2+2*tcoord (a.gaussian i) (a.gaussian j) ∧
      ((p:ℤ) ∣ tcoord (a.gaussian i) (a.gaussian j)^2+xcoord (a.gaussian i) (a.gaussian j)^2 ∨
       (p:ℤ) ∣ tcoord (a.gaussian i) (a.gaussian j)^2+zcoord (a.gaussian i) (a.gaussian j)^2) := by
  obtain ⟨hp,hf⟩ := mixed_chart a i j plus minus
  by_cases dv : p ∣ a.v
  · exact Or.inl dv
  refine Or.inr ⟨?_,hp,hf⟩
  intro dt
  have div := (dvd_add_left (dvd_mul_of_dvd_right dt 2)).mp hp
  have prime := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  exact dv (Int.natCast_dvd_natCast.mp (prime.dvd_of_dvd_pow ((prime.dvd_mul.mp div).resolve_left away)))

theorem inert_divides_parameter {p : ℕ} [Fact p.Prime] (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (away : ¬(p:ℤ) ∣ gap i j) (inert : p%4=3)
    (plus : p ∣ adjacentNorm (a.gaussian i) true)
    (minus : p ∣ adjacentNorm (a.gaussian j) false) : p ∣ a.v := by
  apply (divisor_or_single_chart a i j away plus minus).resolve_right
  rintro ⟨nt,_,_⟩
  have hi := ((inert_iff inert _ true).mp plus).1
  have hj := ((inert_iff inert _ false).mp minus).1
  apply nt
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((tcoord (a.gaussian i) (a.gaussian j):ℤ):ZMod p) = 0
  simp only [tcoord,Int.cast_add]
  change realResidue p (a.gaussian i)+realResidue p (a.gaussian j)=0
  rw [hi,hj]
  norm_num

end Sun28.SieveTail
#print axioms Sun28.SieveTail.hyperbolic
#print axioms Sun28.SieveTail.order_difference
#print axioms Sun28.SieveTail.ray_order_difference_ne_zero
#print axioms Sun28.SieveTail.mixed_chart
#print axioms Sun28.SieveTail.divisor_or_single_chart
#print axioms Sun28.SieveTail.inert_divides_parameter
