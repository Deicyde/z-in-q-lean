import VaryingSections
import PreparedExample

namespace Sun28.PointFibres
open Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses Sun28.PreparedPoles
  Sun28.TwistRank Sun28.TwistExtension ZInQ.RouteK
noncomputable section

/-- The three rational squareclasses that would make a ratio exceptional. -/
def RegularBase (b : ℚ) : Prop :=
  ∀ t : ℚ, t≠0 → b*t^2≠1 ∧ b*t^2≠3 ∧ b*t^2≠9

theorem regular_base {b θ : ℕ} (a : AdmissiblePair b θ) : RegularBase (b:ℚ) := by
  intro t tn
  have sf := Int.squarefree_natCast.mpr a.2.2.1
  have reduce {d : ℕ} (df : Squarefree d) {e : ℚ} (en : e≠0)
      (h : (b:ℚ)*t^2=(d:ℚ)*e^2) : b=d := by
    have L:=sqf_eq_of_eq_mul_sq sf tn (show (b:ℚ)*t^2=(b:ℤ)*t^2 by norm_cast)
    have R:=sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr df) en
      (show (b:ℚ)*t^2=(d:ℤ)*e^2 by exact_mod_cast h)
    exact_mod_cast L.symm.trans R
  have res : b%24=17:=a.2.2.2.2.2.2.2.1
  refine ⟨fun h=>?_,fun h=>?_,fun h=>?_⟩
  · have := reduce (d:=1) squarefree_one (e:=1) one_ne_zero (by simpa using h)
    omega
  · have := reduce (d:=3) Nat.prime_three.squarefree (e:=1) one_ne_zero (by simpa using h)
    omega
  · have := reduce (d:=1) squarefree_one (e:=3) (by norm_num) (by norm_num;exact h)
    omega

def Pencil (b θ : ℚ) : Prop := ∃ t : ℚ, t≠0 ∧ RatioCover b θ t

theorem pencil_of_norm {b θ : ℚ} (bp : 0<b) (H : NormQuartic b θ) : Pencil b θ := by
  obtain ⟨a,c,L,h,cn,Ln,hn,one,two⟩:=H
  let F:=L^2-2*a*L+b
  let G:=9*L^2+6*a*L+b
  change h^2=b*F*G at two
  have fn : F≠0:=by intro z;apply (pow_ne_zero 2 hn);rw [two,z];ring
  let t:=h/(b*F)
  let r:=b*t^2
  have tn : t≠0:=div_ne_zero hn (mul_ne_zero bp.ne' fn)
  have ratio : G=r*F:=by
    unfold r t;field_simp;linear_combination -two
  have p : (9-r)*L^2+2*((3+r)*a)*L+(1-r)*b=0:=by
    dsimp [F,G] at ratio;linear_combination ratio
  refine ⟨t,tn,a,c,(9-r)*L+(3+r)*a,cn,one,?_⟩
  change ((9-r)*L+(3+r)*a)^2=16*b*r+(r+3)^2*θ*c^2
  linear_combination (9-r)*p+(r+3)^2*one

theorem norm_of_pencil {b θ : ℚ} (bp : 0<b) (regular : RegularBase b)
    (P : Pencil b θ) : NormQuartic b θ := by
  obtain ⟨t,tn,a,c,z,cn,one,two⟩:=P
  obtain ⟨r1,r3,r9⟩:=regular t tn
  obtain ⟨L,ln,rel,_,_⟩:=regular_root bp tn one (b*t^2) rfl r1 r3 r9 two
  let F:=L^2-2*a*L+b
  have ratio : 9*L^2+6*a*L+b=(b*t^2)*F:=by dsimp [F];linear_combination rel
  have nz : F≠0:=by
    intro zero
    have G:=ratio
    rw [zero,mul_zero] at G
    dsimp [F] at zero
    have e : 12*L^2+4*b=0:=by linear_combination G+3*zero
    nlinarith only [sq_nonneg L,bp,e]
  exact ⟨a,c,L,b*t*F,cn,ln,mul_ne_zero (mul_ne_zero bp.ne' tn) nz,one,
    by rw [ratio];dsimp [F];ring⟩

theorem norm_iff_pencil {b θ : ℕ} (a : AdmissiblePair b θ) :
    NormQuartic (b:ℚ) (θ:ℚ) ↔ Pencil (b:ℚ) (θ:ℚ) :=
  ⟨pencil_of_norm (by exact_mod_cast a.1),
    norm_of_pencil (by exact_mod_cast a.1) (regular_base a)⟩

theorem nonzero_of_norm {b θ : ℕ} (a : AdmissiblePair b θ) (n : NormQuartic (b:ℚ) (θ:ℚ)) :
    NonzeroPair (b:ℚ) (θ:ℚ) := by
  obtain ⟨t,tn,f⟩:=(norm_iff_pencil a).mp n
  obtain ⟨r1,r3,r9⟩:=regular_base a t tn
  exact nonzero_of_ratio (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) tn r1 r3 r9 f

/-- What remains after all prescribed rational ratios of the norm factors are considered. -/
def PencilResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) → NonzeroPair (b:ℚ) (θ:ℚ)

theorem norm_residual_iff_pencil : NormResidual ↔ PencilResidual := by
  constructor
  · intro f b θ a input fixed conic fac signed out
    apply f b θ a input fixed conic fac signed
    intro n
    obtain ⟨t,tn,e⟩:=(norm_iff_pencil a).mp n
    exact out t tn e
  · intro f b θ a input fixed conic fac signed out
    exact f b θ a input fixed conic fac signed fun t tn e=>out ((norm_iff_pencil a).mpr ⟨t,tn,e⟩)

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.regular_base
#print axioms Sun28.PointFibres.pencil_of_norm
#print axioms Sun28.PointFibres.norm_of_pencil
#print axioms Sun28.PointFibres.norm_iff_pencil
#print axioms Sun28.PointFibres.nonzero_of_norm
#print axioms Sun28.PointFibres.norm_residual_iff_pencil
