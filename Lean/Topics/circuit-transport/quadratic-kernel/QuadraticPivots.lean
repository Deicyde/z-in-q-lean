import Std

namespace CircuitTransport.Quadratic

/-- A rational square that is an integer has a square numerator in lowest terms. -/
theorem no_square_in_gap {n k : Nat} (lower : k^2<n) (upper : n<(k+1)^2) (x : Rat) :
    x^2≠(n:Rat) := by
  intro h
  have numerator : x.num^2=(n:Int) := congrArg Rat.num h
  have size : x.num.natAbs^2=n := by simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs numerator
  by_cases small : x.num.natAbs≤k
  · have bound := Nat.pow_le_pow_left small 2
    rw [size] at bound
    omega
  · have bound := Nat.pow_le_pow_left (show k+1≤x.num.natAbs by omega) 2
    rw [size] at bound
    omega

theorem two_nonsquare (x : Rat) : x^2≠2 :=
  no_square_in_gap (n:=2) (k:=1) (by decide) (by decide) x

/-- The determinant of multiplication by `a+b√2` in the rational basis `1,√2`. -/
def norm (a b : Rat) := a^2-2*b^2

theorem norm_zero_iff (a b : Rat) : norm a b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    unfold norm at h
    by_cases hb : b=0
    · rw [hb] at h
      have aa : a*a=0 := by grobner
      exact ⟨(Rat.mul_eq_zero.mp aa).elim id id,hb⟩
    · have nz : b^2≠0 := by
        intro z
        have bb : b*b=0 := by grobner
        exact (Rat.mul_eq_zero.mp bb).elim hb hb
      let x := a/b
      have xb : x*b=a := Rat.div_mul_cancel hb
      have zero : (x^2-2)*b^2=0 := by
        calc (x^2-2)*b^2 = (x*b)^2-2*b^2 := by grobner
             _ = 0 := by rw [xb]; exact h
      have bad := (Rat.mul_eq_zero.mp zero).resolve_right nz
      exact False.elim (two_nonsquare x (by grobner))
  · rintro ⟨rfl,rfl⟩; unfold norm; grobner

def det (a b c d : Rat) := a*d-b*c

/-- Row-by-row clearing by arbitrary nonzero rational scalars preserves the rank dichotomy. -/
theorem scaled_det_zero_iff (a b r s : Rat) (hr : r≠0) (hs : s≠0) :
    det (r*a) (r*(2*b)) (s*b) (s*a)=0 ↔ a=0 ∧ b=0 := by
  have factor : det (r*a) (r*(2*b)) (s*b) (s*a) = r*(s*norm a b) := by
    unfold det norm; grobner
  rw [factor,←norm_zero_iff]
  constructor
  · intro prod
    exact (Rat.mul_eq_zero.mp ((Rat.mul_eq_zero.mp prod).resolve_left hr)).resolve_left hs
  · intro zero; rw [zero]; grobner

/-- Thus a singular scaled multiplication matrix has every entry zero. -/
theorem scaled_no_rank_one (a b r s : Rat) (hr : r≠0) (hs : s≠0)
    (singular : det (r*a) (r*(2*b)) (s*b) (s*a)=0) :
    r*a=0 ∧ r*(2*b)=0 ∧ s*b=0 ∧ s*a=0 := by
  obtain ⟨rfl,rfl⟩ := (scaled_det_zero_iff a b r s hr hs).mp singular
  exact ⟨by grobner,by grobner,by grobner,by grobner⟩

/-- Components of `513 w² - 1526 w + 1073`, with `w=x+y√2`. -/
def g0 (x y : Rat) := 513*(x^2+2*y^2)-1526*x+1073

def g1 (x y : Rat) := 1026*x*y-1526*y

/-- The discriminant is neither a square nor twice a square over the rationals. -/
theorem discriminant_nonsquare (x : Rat) : x^2≠126880 ∧ x^2≠63440 :=
  ⟨no_square_in_gap (n:=126880) (k:=356) (by decide) (by decide) x,
   no_square_in_gap (n:=63440) (k:=251) (by decide) (by decide) x⟩

/-- The quadratic has no root in `Q(√2)`, expressed in rational coordinates. -/
theorem pade_nonzero (x y : Rat) : ¬(g0 x y=0 ∧ g1 x y=0) := by
  rintro ⟨real,imag⟩
  let u := 1026*x-1526
  let v := 1026*y
  have completed : u^2+2*v^2=126880 := by
    have id : u^2+2*v^2=2052*g0 x y+126880 := by dsimp [u,v,g0]; grobner
    rw [id,real]; grobner
  have uv : u*v=0 := by
    have id : u*v=1026*g1 x y := by dsimp [u,v,g1]; grobner
    rw [id,imag]; grobner
  rcases Rat.mul_eq_zero.mp uv with hz|hz
  · rw [hz] at completed
    exact (discriminant_nonsquare v).2 (by grobner)
  · rw [hz] at completed
    exact (discriminant_nonsquare u).1 (by grobner)

/-- Physical multiplier `480675*g((11-6√2)(x+2y√2))` has nonzero rational determinant. -/
theorem physical_pade_det (x y : Rat) :
    let w₀ := 11*x-24*y
    let w₁ := 22*y-6*x
    let A := 480675*g0 w₀ w₁
    let B := 480675*g1 w₀ w₁
    det A (2*B) B A ≠ 0 := by
  dsimp only
  let w₀ := 11*x-24*y
  let w₁ := 22*y-6*x
  let a := g0 w₀ w₁
  let b := g1 w₀ w₁
  change det (480675*a) (2*(480675*b)) (480675*b) (480675*a) ≠ 0
  intro singular
  have zero : det (480675*a) (480675*(2*b)) (480675*b) (480675*a)=0 := by
    rw [show (480675:Rat)*(2*b)=2*(480675*b) by grobner]; exact singular
  have both := (scaled_det_zero_iff a b 480675 480675 (by decide) (by decide)).mp zero
  exact pade_nonzero w₀ w₁ both

#print axioms no_square_in_gap
#print axioms two_nonsquare
#print axioms norm_zero_iff
#print axioms scaled_det_zero_iff
#print axioms scaled_no_rank_one
#print axioms discriminant_nonsquare
#print axioms pade_nonzero
#print axioms physical_pade_det

end CircuitTransport.Quadratic
