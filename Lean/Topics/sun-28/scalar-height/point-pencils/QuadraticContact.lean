import ScalarEstimates

/-! Height recovery from the tangent to a diagonal conic at an integral seed. -/
namespace Sun28.PointPencils

def form (l m a b : ℤ) : ℤ := l*a^2+m*b^2
def det (u v a b : ℤ) : ℤ := u*b-v*a
def polar (l m u v a b : ℤ) : ℤ := l*u*a+m*v*b

theorem tangent_identity (l m u v a b : ℤ) :
    form l m u v * form l m a b - (polar l m u v a b)^2 =
      l*m*(det u v a b)^2 := by unfold form polar det; ring

private theorem bound_polar {p z n : ℤ} (hn : n≠0) (h : (z-p)*(z+p)=n) :
    |p| ≤|n| := by
  have nz : (z-p)*(z+p)≠0 := h ▸ hn
  have u : 1≤|z-p| := abs_pos.mpr (left_ne_zero_of_mul nz)
  have v : 1≤|z+p| := abs_pos.mpr (right_ne_zero_of_mul nz)
  have eq := congrArg abs h
  rw [abs_mul] at eq
  have hu : |z-p| ≤|n| := eq ▸ le_mul_of_one_le_right (abs_nonneg _) v
  have hv : |z+p| ≤|n| := eq ▸ le_mul_of_one_le_left (abs_nonneg _) u
  apply abs_le.mpr
  constructor <;> linarith only [hu,hv,le_abs_self (z-p),neg_abs_le (z-p),
    le_abs_self (z+p),neg_abs_le (z+p)]

private theorem recover {q a p k u m v H B : ℤ} (eq : q*a=u*p+m*v*k)
    (cap : |p| ≤B*k^2) (hu : |u| ≤H) (hv : |v| ≤H) (hk : k≠0) :
    |a| *|q| ≤ H*(B+|m|)*k^2 := by
  have ko : 1≤|k| := abs_pos.mpr hk
  have kk : |k| ≤k^2 := by
    calc |k| ≤ |k| *|k| := le_mul_of_one_le_right (abs_nonneg _) ko
         _ = k^2 := by rw [←sq,sq_abs]
  have first := mul_le_mul hu cap (abs_nonneg p) ((abs_nonneg u).trans hu)
  have second := mul_le_mul hv kk (abs_nonneg k) ((abs_nonneg v).trans hv)
  calc
    |a| *|q| = |q*a| := by rw [abs_mul,mul_comm]
    _ ≤ |u| *|p| +|m| *(|v| *|k|) := by
      rw [eq]
      simpa only [abs_mul,mul_assoc] using (abs_add_le (u*p) (m*v*k))
    _ ≤ H*(B*k^2)+|m| *(H*k^2) := add_le_add first (mul_le_mul_of_nonneg_left second (abs_nonneg _))
    _ = _ := by ring

/-- The factor |Q(u,v)| is retained even for indefinite quadratic forms. -/
theorem coordinates_of_square {l m u v a b : ℤ} (hl : l≠0) (hm : m≠0)
    (away : det u v a b≠0) (square : IsSquare (form l m u v*form l m a b)) :
    max |a| |b| *|form l m u v| ≤
      max |u| |v| *(|l*m| +max |l| |m|)*(det u v a b)^2 := by
  let q:=form l m u v
  let p:=polar l m u v a b
  let k:=det u v a b
  let H:=max |u| |v|
  let D:=max |l| |m|
  obtain ⟨z,hz⟩:=square
  have id:=tangent_identity l m u v a b
  rw [hz] at id
  have fac : (z-p)*(z+p)=l*m*k^2 := by dsimp only [p,k];linear_combination id
  have cap:=bound_polar (mul_ne_zero (mul_ne_zero hl hm) (pow_ne_zero 2 away)) fac
  rw [abs_mul,abs_of_nonneg (sq_nonneg k)] at cap
  have ea : q*a=u*p+(-m)*v*k := by dsimp [q,p,k,form,det,polar];ring
  have eb : q*b=v*p+l*u*k := by dsimp [q,p,k,form,det,polar];ring
  have au:=recover ea cap (le_max_left ..) (le_max_right ..) away
  have bu:=recover eb cap (le_max_right |u| |v|) (le_max_left ..) away
  rw [abs_neg] at au
  have bigger (e : ℤ) (small : e≤D) :
      H*(|l*m| +e)*k^2≤H*(|l*m| +D)*k^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ((abs_nonneg u).trans (le_max_left ..))) (sq_nonneg k)
  change max |a| |b| *|q| ≤H*(|l*m| +D)*k^2
  rw [max_mul_of_nonneg _ _ (abs_nonneg _)]
  exact max_le (au.trans (bigger _ (le_max_right ..))) (bu.trans (bigger _ (le_max_left ..)))

end Sun28.PointPencils
#print axioms Sun28.PointPencils.tangent_identity
#print axioms Sun28.PointPencils.coordinates_of_square
