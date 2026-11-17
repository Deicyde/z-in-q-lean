import NormBounds
import FiniteIndex
import Mathlib.NumberTheory.Zsqrtd.ToReal

namespace EllipticHeight.PhysicalOrder
open EllipticHeight.NormBounds

abbrev O := Zsqrtd (2 : ℤ)

noncomputable def realNorm : NormData O where
  norm := Zsqrtd.normMonoidHom
  plus := Zsqrtd.lift ⟨Real.sqrt 2, by norm_num [Real.mul_self_sqrt]⟩
  minus := Zsqrtd.lift ⟨-Real.sqrt 2, by norm_num [Real.mul_self_sqrt]⟩
  factor := by
    intro z
    change ((z.re*z.re-2*z.im*z.im : ℤ):ℝ) =
      ((z.re:ℝ)+z.im*Real.sqrt 2)*((z.re:ℝ)+z.im*(-Real.sqrt 2))
    push_cast
    linear_combination (z.im:ℝ)^2*(Real.sq_sqrt (by norm_num : (0:ℝ)≤2))

def D : O := ⟨11,-6⟩
def A1 : O := ⟨57,-28⟩
def B1 : O := 8
def rawA (a b : O) := (a^2+D*b^2)^2
def rawB (a b : O) := 4*a*b*(a^2-D*b^2)
def A2 : O := rawA A1 B1
def B2 : O := rawB A1 B1

/-- R=(1+√2,2√2), its equation, and the exact projective cancellation by 4
in the double x(P)=[57−28√2:8]. -/
theorem first_double :
    let x : O := ⟨1,1⟩
    let y : O := ⟨0,2⟩
    y^2 = x^3-D*x ∧ rawA x 1 = 4*A1 ∧ rawB x 1 = 4*B1 := by decide

theorem primitive_first : ∃ u v : O, u*A1+v*B1=1 := by
  exact ⟨A1,⟨-602,399⟩,by decide⟩

theorem primitive_second : ∃ u v : O, u*A2+v*B2=1 := by
  exact ⟨⟨52858577378065996129,37233248226446440176⟩,
    ⟨-144067443606783356544,-101228887789697733120⟩,by decide⟩

theorem generator_masses : mass realNorm (1:O)=1 ∧
    mass realNorm A1=41^2 ∧ mass realNorm A2=4905889^2 := by decide

private theorem raw_grows (a b : O)
    (dp : 0 ≤ realNorm.plus (D*b^2)) (dm : 0 ≤ realNorm.minus (D*b^2))
    (bp : realNorm.plus (D*b^2) ≤ (realNorm.plus a)^2)
    (bm : realNorm.minus (D*b^2) ≤ (realNorm.minus a)^2) :
    (mass realNorm a)^4 ≤ mass realNorm (rawA a b) ∧
      mass realNorm (rawA a b) ≤ 16*(mass realNorm a)^4 :=
  double_raw realNorm D a b dp dm bp bm

/-- A single real expanding-branch check on each point gives the paired inequality. -/
theorem branch_pair (D a b c e : ℝ) (pos : 0 ≤ D)
    (u : D*b^2 ≤ a^2) (v : D*e^2 ≤ c^2) : |D*b*e| ≤ |a*c| := by
  apply sq_le_sq.mp
  have z := mul_le_mul u v (mul_nonneg pos (sq_nonneg _)) (sq_nonneg a)
  nlinarith only [z]

/-- Two positive finite abscissae, or homogeneous infinity [1:0], also
make the paired numerator nonzero on both real branches. -/
theorem branch_live (D a b c e : ℝ) (pos : 0 ≤ D) (ha : a ≠ 0) (hc : c ≠ 0)
    (u : 0 ≤ a*b) (v : 0 ≤ c*e) : a*c+D*b*e ≠ 0 := by
  intro z
  have w := mul_nonneg pos (mul_nonneg u v)
  have k := mul_pos (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hc)
  have m := congrArg (fun x : ℝ => x*(a*c)) z
  nlinarith only [m,w,k]

/-- Geometric coordinate information needed on the finite list of points.
The numerator and denominator permit multiplication by any common unit.
The last two fields are the homogeneous addition-law cross-products. -/
structure Coordinates (A B : ℕ → O) (n : ℕ) : Prop where
  numeratorLive : ∀ i, realNorm.norm (A i) ≠ 0
  origin : mass realNorm (A 0) = mass realNorm 1
  first : mass realNorm (A 1) = mass realNorm A1
  second : mass realNorm (A 2) = mass realNorm A2
  primitive : ∀ i, ∃ u v : O, u*A i+v*B i=1
  plusBranch : ∀ i, realNorm.plus (D*(B i)^2) ≤ (realNorm.plus (A i))^2
  minusBranch : ∀ i, realNorm.minus (D*(B i)^2) ≤ (realNorm.minus (A i))^2
  plusSign : ∀ i, 0 ≤ realNorm.plus (A i)*realNorm.plus (B i)
  minusSign : ∀ i, 0 ≤ realNorm.minus (A i)*realNorm.minus (B i)
  evenRaw : ∀ i, mass realNorm (rawA (A (2*i)) (B (2*i))) = mass realNorm (A (4*i))
  lastRaw : A (2*n) ∣ rawA (A n) (B n)
  middle : ∀ j : ℕ, j+2 ≤ n →
    let a := A (2*(j+2)); let b := B (2*(j+2))
    let c := A (2*j); let e := B (2*j)
    let i := 4*(j+1)
    (a*c+D*b*e)^2*(A i*B 4+B i*A 4) = (2*(a*e+b*c)*(a*c-D*b*e))*(A i*A 4)
  bottom : ∀ j : ℕ, j+2 ≤ n →
    let a := A (2*(j+2)); let b := B (2*(j+2))
    let c := A (2*j); let e := B (2*j)
    let i := 4*(j+1)
    (a*c+D*b*e)^2*(B i*B 4) = (a*e-b*c)^2*(A i*A 4)

private theorem positiveD : 0 ≤ realNorm.plus D ∧ 0 ≤ realNorm.minus D := by
  change 0 ≤ ((11:ℤ):ℝ)+((-6:ℤ):ℝ)*Real.sqrt 2 ∧ 0 ≤ ((11:ℤ):ℝ)+((-6:ℤ):ℝ)*(-Real.sqrt 2)
  norm_num1
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  constructor <;> nlinarith [sq_nonneg (Real.sqrt 2-2), Real.sqrt_nonneg (2:ℝ)]

/-- A finite, real-quadratic-order specialization giving the exact integer
bound needed by the raw circuit numerator. -/
theorem physical_numerator_index (A B : ℕ → O) (n : ℕ) (hn : n≠0)
    (g : Coordinates A B n) : (41^(n^2))^2 ≤ (A n).norm.natAbs := by
  change (41^(n^2))^2 ≤ mass realNorm (A n)
  let W i := mass realNorm (A i)
  have livePlus (i : ℕ) : realNorm.plus (A i) ≠ 0 := by
    intro z
    have e := realNorm.factor (A i)
    rw [z,zero_mul] at e
    exact g.numeratorLive i (by exact_mod_cast e)
  have liveMinus (i : ℕ) : realNorm.minus (A i) ≠ 0 := by
    intro z
    have e := realNorm.factor (A i)
    rw [z,mul_zero] at e
    exact g.numeratorLive i (by exact_mod_cast e)
  have plusB (i : ℕ) : 0 ≤ realNorm.plus (D*(B i)^2) := by
    rw [map_mul,map_pow]; exact mul_nonneg positiveD.1 (sq_nonneg _)
  have minusB (i : ℕ) : 0 ≤ realNorm.minus (D*(B i)^2) := by
    rw [map_mul,map_pow]; exact mul_nonneg positiveD.2 (sq_nonneg _)
  have dup (i : ℕ) := raw_grows (A i) (B i) (plusB i) (minusB i) (g.plusBranch i) (g.minusBranch i)
  have even (i : ℕ) : W (2*i)^4 ≤ W (4*i) := (dup (2*i)).1.trans_eq (g.evenRaw i)
  obtain ⟨w0,w1,w2⟩ := generator_masses
  apply EllipticHeight.FiniteIndex.integer_numerator_index W n hn (fun i => Int.natAbs_pos.2 (g.numeratorLive i))
    (g.origin.trans w0) (g.first.trans w1) (g.second.trans w2) (fun j _ => even (j+1)) (even 1)
  · intro j hj
    let u := 2*(j+2); let v := 2*j
    have bound (f : O →+* ℝ) (fd : 0 ≤ f D)
        (atU : f (D*(B u)^2) ≤ (f (A u))^2) (atV : f (D*(B v)^2) ≤ (f (A v))^2) :
        |f (D*B u*B v)| ≤ |f (A u*A v)| := by
      simp only [map_mul,map_pow] at *
      exact branch_pair _ _ _ _ _ fd atU atV
    have live (f : O →+* ℝ) (fd : 0 ≤ f D) (nz : ∀ i, f (A i) ≠ 0)
        (ss : ∀ i, 0 ≤ f (A i)*f (B i)) : f (A u*A v+D*B u*B v) ≠ 0 := by
      simp only [map_add,map_mul]; exact branch_live _ _ _ _ _ fd (nz u) (nz v) (ss u) (ss v)
    have realLive := mul_ne_zero (live _ positiveD.1 livePlus g.plusSign)
      (live _ positiveD.2 liveMinus g.minusSign)
    rw [← realNorm.factor] at realLive
    exact paired_numerator realNorm D (A u) (B u) (A v) (B v) _ _ _ _
      (g.primitive _) (g.primitive _) (g.middle j hj) (g.bottom j hj) (by exact_mod_cast realLive)
      (bound _ positiveD.1 (g.plusBranch _) (g.plusBranch _))
      (bound _ positiveD.2 (g.minusBranch _) (g.minusBranch _))
  · have nz : realNorm.norm (rawA (A n) (B n)) ≠ 0 := by
      intro bad
      have zeroMass : mass realNorm (rawA (A n) (B n))=0 := by simp [mass,bad]
      have lo := (dup n).1
      rw [zeroMass] at lo
      have p := Nat.pow_pos (Int.natAbs_pos.2 (g.numeratorLive n)) (n:=4)
      exact (Nat.not_lt_of_ge lo) p
    exact (mass_divides_bound realNorm _ _ g.lastRaw nz).trans (dup n).2

#print axioms realNorm
#print axioms first_double
#print axioms primitive_first
#print axioms primitive_second
#print axioms generator_masses
#print axioms branch_pair
#print axioms branch_live
#print axioms physical_numerator_index
end EllipticHeight.PhysicalOrder
