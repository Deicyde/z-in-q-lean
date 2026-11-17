import PhysicalOrder

namespace EllipticHeight.SignedOrder
open EllipticHeight.NormBounds EllipticHeight.PhysicalOrder

def Primitive {R : Type*} [CommRing R] (a b : R) : Prop := ∃ u v, u*a+v*b=1

/-- A unimodular homogeneous pair generates any cross-equal pair by a common scalar. -/
theorem projective_scale {R : Type*} [CommRing R] {a b c d : R}
    (pr : Primitive a b) (cross : a*d=b*c) : ∃ s : R, c=s*a ∧ d=s*b := by
  obtain ⟨u,v,bez⟩ := pr
  refine ⟨u*c+v*d, ?_, ?_⟩
  · calc
      c = c*(u*a+v*b) := by rw [bez,mul_one]
      _ = _ := by linear_combination (-v)*cross
  · calc
      d = d*(u*a+v*b) := by rw [bez,mul_one]
      _ = _ := by linear_combination u*cross

theorem projective_divides {R : Type*} [CommRing R] {a b c d : R}
    (pr : Primitive a b) (cross : a*d=b*c) : a ∣ c := by
  obtain ⟨s,ha,_⟩ := projective_scale pr cross
  exact ⟨s,ha.trans (mul_comm s a)⟩

private theorem mass_dvd {R : Type*} [CommRing R] (d : NormData R) {a b : R}
    (dvd : a ∣ b) : mass d a ∣ mass d b := by
  obtain ⟨s,rfl⟩ := dvd
  exact ⟨mass d s,by simp [mass, Int.natAbs_mul]⟩

/-- Mutual divisibility also handles a zero numerator and requires no chosen unit. -/
theorem projective_mass {R : Type*} [CommRing R] (N : NormData R) {a b c d : R}
    (p : Primitive a b) (q : Primitive c d) (cross : a*d=b*c) :
    mass N a=mass N c := by
  have rev : c*b=d*a := by linear_combination -cross
  exact Nat.dvd_antisymm (mass_dvd N (projective_divides p cross)) (mass_dvd N (projective_divides q rev))

def RealQuartic (D a b : ℝ) : Prop :=
  b=0 ∨ ∃ h j : ℝ, a=b*h^2 ∧ j^2=h^4-D

/-- The real quartic gives both projective branch inequalities and excludes
numerator zero. The case b=0 represents the point at infinity. -/
theorem quartic_branch {D a b : ℝ} (pos : 0<D) (nz : a≠0 ∨ b≠0)
    (chart : RealQuartic D a b) : a≠0 ∧ D*b^2≤a^2 ∧ 0≤a*b := by
  rcases chart with hb | ⟨h,j,ha,hj⟩
  · subst b
    exact ⟨nz.resolve_right (by simp),by simp [sq_nonneg],by simp⟩
  · have hn : h≠0 := by
      rintro rfl
      norm_num at hj
      nlinarith [sq_nonneg j]
    have bn : b≠0 := by
      intro bb
      have az : a=0 := by simp [ha,bb]
      exact nz.elim (fun z => z az) (fun z => z bb)
    have u := mul_le_mul_of_nonneg_left (show D≤h^4 by nlinarith [sq_nonneg j]) (sq_nonneg b)
    have s := mul_nonneg (sq_nonneg b) (sq_nonneg h)
    rw [ha]
    refine ⟨mul_ne_zero bn (pow_ne_zero 2 hn), ?_, ?_⟩ <;> nlinarith only [u,s]

private theorem image_nontrivial {R : Type*} [CommRing R] (f : R →+* ℝ) {a b : R}
    (pr : Primitive a b) : f a ≠ 0 ∨ f b ≠ 0 := by
  by_contra! bad
  obtain ⟨u,v,bez⟩ := pr
  have z := congrArg f bez
  simp [bad.1,bad.2] at z

/-- A weighted integral chart gives the square abscissa and the signed ordinate
at every real embedding, including the homogeneous input with denominator zero. -/
theorem quartic_of_chart (x y z : O) (chart : z^2 + D*y^4 = x^4) (f : O →+* ℝ) :
    RealQuartic (f D) (f (x^2)) (f (y^2)) := by
  have eqn := congrArg f chart
  simp only [map_add,map_mul,map_pow] at eqn
  by_cases hy : f y=0
  · left; simp [hy]
  · right
    refine ⟨f x/f y, f z/(f y)^2, ?_, ?_⟩
    · rw [map_pow,map_pow,div_pow]
      field_simp
    · field_simp
      linear_combination eqn

private theorem positiveD : 0<realNorm.plus D ∧ 0<realNorm.minus D := by
  change 0 < ((11:ℤ):ℝ)+((-6:ℤ):ℝ)*Real.sqrt 2 ∧ 0 < ((11:ℤ):ℝ)+((-6:ℤ):ℝ)*(-Real.sqrt 2)
  norm_num1
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  constructor <;> nlinarith [sq_nonneg (Real.sqrt 2-2), Real.sqrt_nonneg (2:ℝ)]

private theorem raw_scale (s a b : O) :
    rawA (s*a) (s*b)=s^4*rawA a b ∧ rawB (s*a) (s*b)=s^4*rawB a b := by
  constructor <;> dsimp [rawA,rawB] <;> ring

structure SignedCoordinates (A B : ℕ → O) (n : ℕ) : Prop where
  primitive : ∀ i, Primitive (A i) (B i)
  origin : B 0=0
  generator : A 1*B1=B 1*A1
  quartic : ∀ i (f : O →+* ℝ), RealQuartic (f D) (f (A i)) (f (B i))
  doubleCross : ∀ i, rawA (A i) (B i)*B (2*i)=rawB (A i) (B i)*A (2*i)
  rawPrimitive : ∀ i, Primitive (rawA (A (2*i)) (B (2*i))) (rawB (A (2*i)) (B (2*i)))
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

theorem SignedCoordinates.coordinates {A B : ℕ → O} {n : ℕ} (g : SignedCoordinates A B n) :
    Coordinates A B n := by
  have branch (i : ℕ) (f : O →+* ℝ) (pos : 0<f D) :
      f (A i) ≠ 0 ∧ f (D*(B i)^2) ≤ (f (A i))^2 ∧ 0≤f (A i)*f (B i) := by
    simpa only [map_mul,map_pow] using quartic_branch pos (image_nontrivial f (g.primitive i)) (g.quartic i f)
  refine {
    numeratorLive := fun i bad => ?_
    origin := ?_
    first := projective_mass realNorm (g.primitive 1) primitive_first g.generator
    second := ?_
    primitive := g.primitive
    plusBranch := fun i => (branch i _ positiveD.1).2.1
    minusBranch := fun i => (branch i _ positiveD.2).2.1
    plusSign := fun i => (branch i _ positiveD.1).2.2
    minusSign := fun i => (branch i _ positiveD.2).2.2
    evenRaw := fun i => ?_
    lastRaw := ?_
    middle := g.middle
    bottom := g.bottom }
  · have nz := mul_ne_zero (branch i _ positiveD.1).1 (branch i _ positiveD.2).1
    have z := realNorm.factor (A i)
    rw [bad,Int.cast_zero] at z
    exact nz z.symm
  · apply projective_mass realNorm (g.primitive 0) (show Primitive (1:O) 0 from ⟨1,0,by ring⟩)
    rw [g.origin]; ring
  · apply projective_mass realNorm (g.primitive 2) primitive_second
    obtain ⟨s,hs,ht⟩ := projective_scale (g.primitive 1) g.generator
    have d := g.doubleCross 1
    norm_num1 at d
    unfold A2 B2
    rw [hs,ht,(raw_scale s (A 1) (B 1)).1,(raw_scale s (A 1) (B 1)).2]
    linear_combination (-(s^4))*d
  · have h := projective_mass realNorm (g.rawPrimitive i) (g.primitive (2*(2*i))) (g.doubleCross (2*i))
    simpa only [← Nat.mul_assoc] using h
  · have rev : A (2*n)*rawB (A n) (B n)=B (2*n)*rawA (A n) (B n) := by
      linear_combination -(g.doubleCross n)
    exact projective_divides (g.primitive (2*n)) rev

/-- Sharp integer growth from ordinary projective and signed-quartic data. -/
theorem signed_numerator_index (A B : ℕ → O) (n : ℕ) (hn : n≠0)
    (g : SignedCoordinates A B n) : (41^(n^2))^2 ≤ (A n).norm.natAbs :=
  physical_numerator_index A B n hn g.coordinates

#print axioms projective_scale
#print axioms projective_divides
#print axioms projective_mass
#print axioms quartic_branch
#print axioms quartic_of_chart
#print axioms SignedCoordinates.coordinates
#print axioms signed_numerator_index
end EllipticHeight.SignedOrder
