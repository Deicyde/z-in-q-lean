import CrossRatioForms
import ZInQKernel.RouteK.Slots.Basic

/-! The exact genus-two sextic obtained by the quadratic coordinate t=(A-B)/A. -/
namespace Sun28.FiveDescent
open Sun28.Ordinary ZInQ.RouteK

def F1 (A B : ℤ) := A*(A-B)
def F2 (A B : ℤ) := B*A*(A-2401*B)*(32*A+343*B)
def D (A B : ℤ) := sqfInt (F1 A B)
def E (A B : ℤ) := sqfInt (F2 A B)
def cubic (t : ℚ) := (1-t)*(2401*t-2400)*(375-343*t)
def parameter (d : ℤ) (x : ℚ) := (1-(d:ℚ)*x^2)⁻¹
def sextic (d : ℤ) (x : ℚ) := cubic ((d:ℚ)*x^2)

theorem rows {A B : ℤ} (off : ∀ i,oldForm i A B≠0) : A≠0 ∧ B≠0 ∧ F1 A B≠0 ∧ F2 A B≠0 := by
  have a : A≠0 := off 1
  have b : B≠0 := off 0
  have c : A-B≠0 := off 2
  have d : A-2401*B≠0 := off 3
  have e : 32*A+343*B≠0 := off 4
  exact ⟨a,b,mul_ne_zero a c,mul_ne_zero (mul_ne_zero (mul_ne_zero b a) d) e⟩

theorem chart_identity {A B : ℤ} (na : A≠0) :
    let t : ℚ:=((A:ℚ)-B)/A
    (F1 A B:ℚ)=(A:ℚ)^2*t ∧ (F2 A B:ℚ)=(A:ℚ)^4*cubic t := by
  have a : (A:ℚ)≠0 := by exact_mod_cast na
  dsimp [F1,F2,cubic]
  push_cast
  constructor
  · field_simp [a]
  · field_simp [a];ring

/-- Every off-mark primitive slope, and even an unreduced pair, produces an
affine point on the sextic with its two actual signed squarefree coefficients. -/
theorem forward {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    let d:=D A B
    let e:=E A B
    Squarefree d ∧ Squarefree e ∧ ∃ x y : ℚ, x≠0 ∧ y≠0 ∧
      (e:ℚ)*y^2=sextic d x ∧ parameter d x=(A:ℚ)/B := by
  obtain ⟨na,nb,nf,ng⟩:=rows off
  obtain ⟨sd,k,nk,hk⟩:=sqfInt_spec nf
  obtain ⟨se,l,nl,hl⟩:=sqfInt_spec ng
  let a:ℚ:=A
  let b:ℚ:=B
  let d:=D A B
  let e:=E A B
  have an : a≠0 := by dsimp [a];exact_mod_cast na
  have bn : b≠0 := by dsimp [b];exact_mod_cast nb
  let x:ℚ:=k/a
  let y:ℚ:=l/a^2
  have ident:=chart_identity (B:=B) na
  have hd : (F1 A B:ℚ)=(d:ℚ)*(k:ℚ)^2 := by exact_mod_cast hk
  have he : (F2 A B:ℚ)=(e:ℚ)*(l:ℚ)^2 := by exact_mod_cast hl
  have t : (d:ℚ)*x^2=(a-b)/a := by
    change (d:ℚ)*((k:ℚ)/a)^2=(a-b)/a
    field_simp [an]
    change (d:ℚ)*(k:ℚ)^2=a*(a-b)
    rw [←hd];dsimp [a,b,F1];push_cast; rfl
  refine ⟨sd,se,x,y,div_ne_zero (by exact_mod_cast nk) an,
    div_ne_zero (by exact_mod_cast nl) (pow_ne_zero _ an),?_,?_⟩
  · change (e:ℚ)*((l:ℚ)/a^2)^2=cubic ((d:ℚ)*x^2)
    rw [t]
    field_simp [an]
    have lhs : (e:ℚ)*(l:ℚ)^2=a^4*cubic ((a-b)/a) := he.symm.trans ident.2
    linear_combination lhs
  · change (1-(d:ℚ)*x^2)⁻¹=a/b
    rw [t, show (1:ℚ)-(a-b)/a=b/a by field_simp;ring,inv_div]

/-- A squarefree sextic point away from x=0 and the ramification points
determines the signed primitive pair and both homogeneous kernels. -/
theorem inverse {d e : ℤ} {x y : ℚ} (sd : Squarefree d) (se : Squarefree e)
    (nx : x≠0) (ny : y≠0) (point : (e:ℚ)*y^2=sextic d x) :
    let s:=parameter d x
    (∀ i,oldForm i s.num s.den≠0) ∧ D s.num s.den=d ∧ E s.num s.den=e := by
  let t:ℚ:=(d:ℚ)*x^2
  let s:=parameter d x
  have dn : (d:ℚ)≠0 := by exact_mod_cast sd.ne_zero
  have en : (e:ℚ)≠0 := by exact_mod_cast se.ne_zero
  have tn : t≠0 := mul_ne_zero dn (pow_ne_zero _ nx)
  have prod : cubic t≠0 := by rw [←show (e:ℚ)*y^2=cubic t from point];exact mul_ne_zero en (pow_ne_zero _ ny)
  have fa : 1-t≠0 := fun e => prod (by simp [cubic,e])
  have fb : 2401*t-2400≠0 := fun e => prod (by simp [cubic,e])
  have fc : 375-343*t≠0 := fun e => prod (by simp [cubic,e])
  have one : s*(1-t)=1 := inv_mul_cancel₀ fa
  have sn : s≠0 := inv_ne_zero fa
  have a : (s.num:ℚ)≠0 := by exact_mod_cast Rat.num_ne_zero.mpr sn
  have b : (s.den:ℚ)≠0 := by exact_mod_cast s.den_nz
  have sa : (s.num:ℚ)=s*(s.den:ℚ) := (div_eq_iff b).mp (Rat.num_div_den s)
  have back : ((s.num:ℚ)-(s.den:ℚ))/s.num=t := by
    apply (div_eq_iff a).mpr
    rw [sa]
    linear_combination (s.den:ℚ)*one
  have ident:=chart_identity (B:=(s.den:ℤ)) (Rat.num_ne_zero.mpr sn)
  push_cast at ident
  rw [back] at ident
  have f1 : (F1 s.num s.den:ℚ)=(d:ℚ)*((s.num:ℚ)*x)^2 := by rw [ident.1];dsimp [t];ring
  have f2 : (F2 s.num s.den:ℚ)=(e:ℚ)*((s.num:ℚ)^2*y)^2 := by
    rw [ident.2,←show (e:ℚ)*y^2=cubic t from point];ring
  have un : (s.num:ℚ)*x≠0 := mul_ne_zero a nx
  have vn : (s.num:ℚ)^2*y≠0 := mul_ne_zero (pow_ne_zero _ a) ny
  have U : F1 s.num s.den≠0 := by
    have v : (F1 s.num s.den:ℚ)≠0 := f1 ▸ mul_ne_zero dn (pow_ne_zero _ un)
    exact_mod_cast v
  have V : F2 s.num s.den≠0 := by
    have v : (F2 s.num s.den:ℚ)≠0 := f2 ▸ mul_ne_zero en (pow_ne_zero _ vn)
    exact_mod_cast v
  dsimp [F1] at U
  dsimp [F2] at V
  simp only [mul_eq_zero,not_or] at U V
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i <;> simp [oldForm] <;> tauto
  · exact (sqf_intCast _).symm.trans (sqf_eq_of_eq_mul_sq sd un f1)
  · exact (sqf_intCast _).symm.trans (sqf_eq_of_eq_mul_sq se vn f2)

end Sun28.FiveDescent
#print axioms Sun28.FiveDescent.chart_identity
#print axioms Sun28.FiveDescent.forward
#print axioms Sun28.FiveDescent.inverse
