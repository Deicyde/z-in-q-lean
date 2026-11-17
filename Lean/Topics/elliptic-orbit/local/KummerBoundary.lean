import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

namespace EllipticOrbit.KummerBoundary

variable {R F : Type*}

/-- The homogeneous third summation polynomial for y²=x³−Dx, written symmetrically. -/
def triple [CommRing R] (D : R) (u v w : R × R) : Prop :=
  (u.1*v.1*w.2 + u.1*v.2*w.1 + u.2*v.1*w.1 + D*u.2*v.2*w.2)^2 =
    4*(u.1*v.1*w.1)*(u.1*v.2*w.2 + u.2*v.1*w.2 + u.2*v.2*w.1)

/-- The line y=lx+b gives these three elementary symmetric functions,
with multiplicity when the chord is tangent. -/
theorem of_vieta [CommRing R] (D x y z l b : R) (hs : x+y+z=l^2)
    (hp : x*y+x*z+y*z= -D-2*l*b) (ht : x*y*z=b^2) :
    triple D (x,1) (y,1) (z,1) := by
  simp only [triple,mul_one,one_mul]
  rw [hp,hs,ht]
  ring

/-- Distinct abscissas on the affine chord, including lines through a two-torsion point. -/
theorem secant [Field F] (D x u l b : F) (different : x≠u)
    (hx : (l*x+b)^2=x^3-D*x) (hu : (l*u+b)^2=u^3-D*u) :
    triple D (x,1) (u,1) (l^2-x-u,1) := by
  apply of_vieta D x u (l^2-x-u) l b (by ring)
  · apply mul_left_cancel₀ (sub_ne_zero.mpr different)
    linear_combination hx - hu
  · apply mul_left_cancel₀ (sub_ne_zero.mpr different)
    linear_combination u*hx - x*hu

/-- The tangent case uses its derivative instead of dividing by an abscissa difference. -/
theorem tangent [CommRing R] (D x l b : R) (hx : (l*x+b)^2=x^3-D*x)
    (deriv : 2*(l*x+b)*l=3*x^2-D) : triple D (x,1) (x,1) (l^2-2*x,1) := by
  apply of_vieta D x x (l^2-2*x) l b (by ring)
  · linear_combination deriv
  · linear_combination x*deriv - hx

theorem infinity [CommRing R] (D a b : R) :
    triple D (1,0) (a,b) (a,b) ∧ triple D (a,b) (1,0) (a,b) ∧
      triple D (a,b) (a,b) (1,0) := by
  refine ⟨?_,?_,?_⟩ <;> dsimp [triple] <;> ring

/-- Scaling any of the three homogeneous pairs preserves the equation. -/
theorem scale [CommRing R] {D : R} {u v w : R × R} (h : triple D u v w) (p q s : R) :
    triple D (p*u.1,p*u.2) (q*v.1,q*v.2) (s*w.1,s*w.2) := by
  dsimp [triple] at h ⊢
  linear_combination (p*q*s)^2*h

/-- Recover the single homogeneous equation from the two established
symmetric addition identities before reducing modulo a prime. -/
theorem of_cross [CommRing R] [IsDomain R] (D : R) (u v plus minus : R × R)
    (live : plus.1*minus.1≠0)
    (middle : (u.1*v.1+D*u.2*v.2)^2*(plus.1*minus.2+plus.2*minus.1)
      = 2*(u.1*v.2+u.2*v.1)*(u.1*v.1-D*u.2*v.2)*(plus.1*minus.1))
    (bottom : (u.1*v.1+D*u.2*v.2)^2*(plus.2*minus.2)
      = (u.1*v.2-u.2*v.1)^2*(plus.1*minus.1)) :
    triple D u v plus := by
  dsimp [triple]
  apply mul_left_cancel₀ live
  linear_combination plus.1*plus.2*middle - plus.1^2*bottom

def live [Zero F] (u : F × F) := u.1 ≠ 0 ∨ u.2 ≠ 0
def mark [Zero F] (t : Bool) (u : F × F) := if t then u.1=0 else u.2=0

/-- At the two marked projective points, addition is the parity truth table.
The proof makes sense in every characteristic, including two. -/
theorem boundary [CommRing F] [IsDomain F] {D : F} (hD : D≠0) {u v w : F × F}
    (hu : live u) (hv : live v) (h : triple D u v w) (s t : Bool)
    (us : mark s u) (vt : mark t v) : mark (s.xor t) w := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,e⟩
  rcases w with ⟨f,g⟩
  cases s <;> cases t <;> simp_all [live,mark,triple,Bool.xor,mul_eq_zero]

/-- A finite line of additions of the same point. -/
def ladder [CommRing R] (D : R) (X : ℕ → R × R) (s count : ℕ) : Prop :=
  ∀ k, k < count → triple D (X (s*k)) (X s) (X (s*(k+1)))

private theorem poles [CommRing F] [IsDomain F] {X : ℕ → F × F} {s count : ℕ} {D : F}
    (hD : D≠0) (valid : ∀ i, live (X i)) (origin : (X 0).2=0)
    (hs : (X s).2=0) (rows : ladder D X s count) :
    ∀ k, k≤count → (X (s*k)).2=0 := by
  intro k
  induction k with
  | zero => simp [origin]
  | succ k ih =>
    intro hk
    exact boundary hD (valid _) (valid _) (rows k (by omega)) false false (ih (by omega)) hs

private theorem alternating [CommRing F] [IsDomain F] {X : ℕ → F × F} {s count : ℕ} {D : F}
    (hD : D≠0) (valid : ∀ i, live (X i)) (origin : (X 0).2=0)
    (hs : (X s).1=0) (rows : ladder D X s count) : ∀ k, k≤count →
    (k%2=0 → (X (s*k)).2=0) ∧ (k%2=1 → (X (s*k)).1=0) := by
  intro k
  induction k with
  | zero => simp [origin]
  | succ k ih =>
    intro hk
    obtain ⟨even,odd⟩:=ih (by omega)
    constructor
    · intro p
      exact boundary hD (valid _) (valid _) (rows k (by omega)) true true (odd (by omega)) hs
    · intro p
      exact boundary hD (valid _) (valid _) (rows k (by omega)) false true (even (by omega)) hs

private def coords [CommRing R] [CommRing F] (f : R →+* F) (u : R × R) := (f u.1,f u.2)

private theorem map_ladder [CommRing R] [CommRing F] {D : R} {X : ℕ → R × R}
    {s count : ℕ} (h : ladder D X s count) (f : R →+* F) :
    ladder (f D) (fun k => coords f (X k)) s count := by
  intro k hk
  have four : f (4:R)=(4:F) := by simpa only [Nat.cast_ofNat] using (map_natCast f 4)
  simpa [triple,coords,four] using congrArg f (h k hk)

/-- Outside D, a zero at m and a pole at n are incompatible as soon as
some odd multiple of m is a multiple of n. Only the two indicated finite
lists of the integral summation polynomial are assumed. -/
theorem coprime_of_odd_multiple [CommRing R] (D : R) (X : ℕ → R × R) (m n p q : ℕ)
    (primitive : ∀ k, IsCoprime (X k).1 (X k).2) (origin : (X 0).2=0)
    (atD : IsCoprime (X m).1 D) (common : m*p=n*q) (odd : p%2=1)
    (left : ladder D X m p) (right : ladder D X n q) :
    IsCoprime (X m).1 (X n).2 := by
  by_contra fail
  have proper : Ideal.span ({(X m).1,(X n).2} : Set R) ≠ ⊤ := by
    intro top
    exact fail (Ideal.mem_span_pair.mp ((Ideal.eq_top_iff_one _).mp top))
  obtain ⟨M,maximal,inc⟩ := Ideal.exists_le_maximal _ proper
  letI : M.IsMaximal := maximal
  letI : M.IsPrime := maximal.isPrime
  have am : (X m).1 ∈ M := inc (Ideal.subset_span (by simp))
  have bn : (X n).2 ∈ M := inc (Ideal.subset_span (by simp))
  let f := Ideal.Quotient.mk M
  let Y := fun k => coords f (X k)
  have valid (k : ℕ) : live (Y k) := by
    by_contra bad
    have both : f (X k).1 = 0 ∧ f (X k).2=0 := by simpa [live,Y,coords,not_or] using bad
    obtain ⟨a,b,bez⟩:=primitive k
    have impossible := congrArg f bez
    simp [map_add,map_mul,both.1,both.2] at impossible
  have nz : f D ≠ 0 := fun h => Ideal.IsPrime.notMem_of_isCoprime_of_mem atD am
    (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have ori : (Y 0).2=0 := by simp [Y,coords,origin]
  have az : (Y m).1=0 := Ideal.Quotient.eq_zero_iff_mem.mpr am
  have bz : (Y n).2=0 := Ideal.Quotient.eq_zero_iff_mem.mpr bn
  have z := (alternating nz valid ori az (map_ladder left f) p (le_refl _)).2 odd
  have pole := poles nz valid ori bz (map_ladder right f) q (le_refl _)
  rw [← common] at pole
  exact (valid (m*p)).elim (fun a=>a z) (fun b=>b pole)

/-- Signed four-row specialization. Only the companion labels must be odd.
No local group, formal group, or dyadic exceptional-prime input occurs. -/
theorem four_coprime [CommRing R] (D : R) (X : ℕ → R × R) (n : Fin 4 → ℤ) (i : Fin 4)
    (primitive : ∀ k, IsCoprime (X k).1 (X k).2) (origin : (X 0).2=0)
    (atD : IsCoprime (X (n i).natAbs).1 D) (odd : ∀ j, j≠i → n j%2=1)
    (rows : ∀ u v, triple D (X u) (X v) (X (u+v))) :
    IsCoprime (X (n i).natAbs).1 (∏ j, (X (n j).natAbs).2) := by
  apply IsCoprime.prod_right
  intro j _
  by_cases eq : j=i
  · simpa [eq] using primitive (n i).natAbs
  have allRows (s b : ℕ) : ladder D X s b := fun k _ => by
    simpa only [Nat.mul_add,Nat.mul_one] using rows (s*k) s
  have absOdd (z : ℤ) (e : z%2=1) : z.natAbs%2=1 := by cases z <;> omega
  exact coprime_of_odd_multiple D X _ _ _ _ primitive origin atD (Nat.mul_comm _ _)
    (absOdd _ (odd j eq)) (allRows _ _) (allRows _ _)

#print axioms of_vieta
#print axioms secant
#print axioms tangent
#print axioms infinity
#print axioms scale
#print axioms of_cross
#print axioms boundary
#print axioms coprime_of_odd_multiple
#print axioms four_coprime
end EllipticOrbit.KummerBoundary
