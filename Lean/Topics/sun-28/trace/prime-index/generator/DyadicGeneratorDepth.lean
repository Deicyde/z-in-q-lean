import SunPublishedScalar

/-! Dyadic depth growth and a torsion criterion for the actual elliptic group law. -/
namespace Sun28.Scalar
open WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- With integral b, a point of positive parameter depth d doubles to depth
d+v(2) at a dyadic valuation. -/
theorem double_dyadic_depth (w : AddValuation K (WithTop ℤ)) {b : K} (hb : 0≤w b)
    {e : ℤ} (he : 0<e) (h2 : w (2:K)=(e:WithTop ℤ)) (Q : (curve b).Point)
    {d : ℤ} (hd : 0<d) (hz : w (parameter Q)=(d:WithTop ℤ)) :
    w (parameter ((2:ℕ) • Q))=((d+e:ℤ):WithTop ℤ) := by
  cases Q with
  | zero => simp [parameter] at hz
  | some x y h =>
    change w (-x/y)=(d:WithTop ℤ) at hz
    have yn : y≠0 := by rintro rfl; simp at hz
    obtain ⟨u,v,hu,doub,coord⟩ := double_coordinates h yn
    let t := -x/y
    have h4 : w (4:K)=((2*e:ℤ):WithTop ℤ) := by
      rw [show (4:K)=2*2 by norm_num,w.map_mul,h2]
      exact_mod_cast (show e+e=2*e by omega)
    have hterm : (0:WithTop ℤ) < w (4*b*t^4) := by
      rw [w.map_mul,w.map_mul,h4,w.map_pow,show w t=(d:WithTop ℤ) from hz]
      have h : ((2*e:ℤ):WithTop ℤ) ≤ ((2*e:ℤ):WithTop ℤ)+w b := le_add_of_nonneg_right hb
      have h' : ((2*e:ℤ):WithTop ℤ) + 4 • (d:WithTop ℤ) ≤
          (((2*e:ℤ):WithTop ℤ)+w b)+4 • (d:WithTop ℤ) := add_le_add h le_rfl
      apply lt_of_lt_of_le _ h'
      exact_mod_cast (show (0:ℤ)<2*e+4 • d by norm_num [nsmul_eq_mul]; omega)
    have rhs : w (1-4*b*t^4)=0 := by
      rw [w.map_sub_eq_of_lt_left]
      · exact w.map_one
      · rw [w.map_one]; exact hterm
    change u*(4*t^2)=1-4*b*t^4 at coord
    have un : u≠0 := by
      intro eq
      rw [←coord,eq,zero_mul,w.map_zero] at rhs
      exact WithTop.top_ne_coe (a:=0) rhs
    obtain ⟨i,hi⟩ := finite_order w un
    rw [←coord,w.map_mul,w.map_mul,hi,h4,w.map_pow,show w t=(d:WithTop ℤ) from hz] at rhs
    have val : i+(2*e+2*d)=0 := by exact_mod_cast rhs
    have inv : w u⁻¹=((2*(d+e):ℤ):WithTop ℤ) := by
      rw [w.map_inv,hi,show 2*(d+e)= -i by omega]
      rfl
    obtain ⟨a,_,pa,ord⟩ := formal_parameter w hb hu (by omega) inv
    rw [doub]
    change w (-u/v)=_
    rw [pa, show a=d+e by omega]

/-- The dyadic orders of the parameters at all powers-of-two multiples strictly grow. -/
theorem dyadic_iterates (w : AddValuation K (WithTop ℤ)) {b : K} (hb : 0≤w b)
    {e d : ℤ} (he : 0<e) (h2 : w (2:K)=(e:WithTop ℤ))
    (P : (curve b).Point) (hd : 0<d) (init : w (parameter P)=(d:WithTop ℤ)) (n : ℕ) :
    w (parameter ((2^n:ℕ) • P))=((d+(n:ℤ)*e:ℤ):WithTop ℤ) := by
  induction n with
  | zero => simpa using init
  | succ n ih =>
    rw [pow_succ',mul_smul]
    have h := double_dyadic_depth w hb he h2 ((2^n:ℕ) • P)
      (d:=d+(n:ℤ)*e) (by positivity) ih
    rw [h]
    congr 1
    push_cast
    ring

/-- A point of positive finite dyadic depth has infinite order. -/
theorem infinite_of_dyadic_depth (w : AddValuation K (WithTop ℤ)) {b : K} (hb : 0≤w b)
    {e d : ℤ} (he : 0<e) (h2 : w (2:K)=(e:WithTop ℤ))
    (P : (curve b).Point) (hd : 0<d) (init : w (parameter P)=(d:WithTop ℤ)) :
    addOrderOf P=0 := by
  rw [addOrderOf_eq_zero_iff]
  intro finite
  let f (n : ℕ) := (2^n:ℕ) • P
  have inj : Function.Injective f := by
    intro m n eq
    have h := congrArg (fun Q => w (parameter Q)) eq
    change w (parameter ((2^m:ℕ) • P))=w (parameter ((2^n:ℕ) • P)) at h
    rw [dyadic_iterates w hb he h2 P hd init,dyadic_iterates w hb he h2 P hd init] at h
    have ee : d+(m:ℤ)*e=d+(n:ℤ)*e := WithTop.coe_inj.mp h
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt he) (add_left_cancel ee))
  have sub : Set.range f ⊆ (AddSubmonoid.multiples P : Set _) := by
    rintro _ ⟨n,rfl⟩
    exact ⟨2^n,rfl⟩
  exact (Set.infinite_range_of_injective inj) (finite.finite_multiples.subset sub)

end Sun28.Scalar
#print axioms Sun28.Scalar.double_dyadic_depth
#print axioms Sun28.Scalar.dyadic_iterates
#print axioms Sun28.Scalar.infinite_of_dyadic_depth
