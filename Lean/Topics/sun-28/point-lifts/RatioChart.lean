import RatioResidual

namespace Sun28.PointLifts
open Sun28.PointFibres Sun28.PrescribedPoints Sun28.PairedClasses Sun28.TwistExtension
noncomputable section

/-- The normalized abscissas are z and r z, where r is the square ratio of the two marked abscissas divided by θ. -/
structure ConicFibre (b θ s z h j : ℚ) : Prop where
  s_ne : s≠0
  z_ne : z≠0
  first : (z-1)*(z+3)=b*h^2
  second : (s^2/θ*z-1)*(s^2/θ*z+3)=b*j^2

private theorem normalize {b l u y : ℚ} (bn : b≠0) (ln : l≠0) (un : u≠0)
    (E : y^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l)) :
    let z:=b*u^2/l
    (z-1)*(z+3)=b*(y/(b*u*l))^2 := by
  dsimp;field_simp;linear_combination -E

theorem surface_iff_conics {b θ : ℚ} (bp : 0<b) (tn : θ≠0) :
    Surface b θ ↔ ∃ s z h j : ℚ, ConicFibre b θ s z h j := by
  rw [surface_iff_pair bp tn]
  constructor
  · rintro ⟨l,ln,⟨u,y,un,E⟩,⟨v,q,vn,G⟩⟩
    have F:=normalize bp.ne' ln un E
    have J:=normalize bp.ne' (mul_ne_zero ln tn) vn G
    refine ⟨v/u,b*u^2/l,y/(b*u*l),q/(b*v*(l*θ)),div_ne_zero vn un,
      div_ne_zero (mul_ne_zero bp.ne' (pow_ne_zero _ un)) ln,F,?_⟩
    have eq : (v/u)^2/θ*(b*u^2/l)=b*v^2/(l*θ):=by field_simp
    rw [eq];exact J
  · rintro ⟨s,z,h,j,F⟩
    have ln : b/z≠0:=div_ne_zero bp.ne' F.z_ne
    let l:=b/z
    have L : l*z=b:=by dsimp [l];field_simp [F.z_ne]
    let v:=s^2/θ*z
    have V : (l*θ)*v=b*s^2:=by dsimp [l,v];field_simp [F.z_ne]
    have f:=F.first
    have g:(v-1)*(v+3)=b*j^2:=F.second
    refine ⟨l,ln,⟨1,b*l*h,one_ne_zero,?_⟩,⟨s,b*s*l*θ*j,F.s_ne,?_⟩⟩
    · norm_num
      calc
        (b*l*h)^2=b*l^2*(b*h^2):=by ring
        _=b*l^2*((z-1)*(z+3)):=by rw [f]
        _=b*(b-l)*(b+3*l):=by linear_combination b*(l*z+b+2*l)*L
    · calc
        (b*s*l*θ*j)^2=(b*s^2)*(l*θ)^2*(b*j^2):=by ring
        _=(b*s^2)*(l*θ)^2*((v-1)*(v+3)):=by rw [g]
        _=(b*s^2)*(b*s^2-l*θ)*(b*s^2+3*(l*θ)):=by
          linear_combination (b*s^2)*(l*θ*v+b*s^2+2*(l*θ))*V

def abscissa (b u v : ℚ) : ℚ := (u^2+3*b*v^2)/(u^2-b*v^2)

/-- Every point on the first normalized conic has a homogeneous parameter, including its two roots. -/
theorem conic_parameter {b z h : ℚ} (bn : b≠0) (first : (z-1)*(z+3)=b*h^2) :
    ∃ u v : ℚ, (u≠0 ∨ v≠0) ∧ u^2-b*v^2≠0 ∧ z=abscissa b u v := by
  by_cases root : z= -3
  · refine ⟨0,1,Or.inr one_ne_zero,by simpa using bn,?_⟩
    unfold abscissa;rw [root];norm_num;field_simp
  · have n : z+3≠0:=by intro H;apply root;linarith
    have den : (z+3)^2-b*h^2=4*(z+3):=by linear_combination first
    have dn : (z+3)^2-b*h^2≠0:=den ▸ mul_ne_zero (by norm_num) n
    refine ⟨z+3,h,Or.inl n,dn,?_⟩
    unfold abscissa
    apply (eq_div_iff dn).mpr
    linear_combination (z+3)*first

private theorem parameter_equation {b u v : ℚ} (n : u^2-b*v^2≠0) :
    (abscissa b u v-1)*(abscissa b u v+3)=b*(4*u*v/(u^2-b*v^2))^2 := by
  unfold abscissa;field_simp;ring

/-- A single binary quartic for the literal abscissa ratio; neither ordinate is required to be a unit. -/
def singlePolynomial (b θ s u v : ℚ) : ℚ :=
  let L := u^2-b*v^2
  let H := u^2+3*b*v^2
  (s^2*H-θ*L)*(s^2*H+3*θ*L)

def SingleFibre (b θ s : ℚ) : Prop :=
  ∃ u v W : ℚ, (u≠0 ∨ v≠0) ∧ u^2-b*v^2≠0 ∧
    b*W^2=singlePolynomial b θ s u v

theorem conics_iff_single {b θ s : ℚ} (bp : 0<b) (tn : θ≠0) (sn : s≠0) :
    (∃ z h j : ℚ, ConicFibre b θ s z h j) ↔ SingleFibre b θ s := by
  constructor
  · rintro ⟨z,h,j,F⟩
    obtain ⟨u,v,uv,den,eq⟩:=conic_parameter bp.ne' F.first
    refine ⟨u,v,j*θ*(u^2-b*v^2),uv,den,?_⟩
    have g:=F.second
    rw [eq] at g;unfold abscissa at g
    unfold singlePolynomial
    field_simp at g
    linear_combination -g
  · rintro ⟨u,v,W,uv,den,E⟩
    let L:=u^2-b*v^2
    let H:=u^2+3*b*v^2
    have Hp : H≠0:=by
      rcases uv with un|vn
      · dsimp [H];positivity
      · dsimp [H];positivity
    refine ⟨abscissa b u v,4*u*v/L,W/(θ*L),sn,div_ne_zero Hp den,parameter_equation den,?_⟩
    change (s^2/θ*(H/L)-1)*(s^2/θ*(H/L)+3)=b*(W/(θ*L))^2
    change b*W^2=(s^2*H-θ*L)*(s^2*H+3*θ*L) at E
    have nn : L≠0:=den
    field_simp
    linear_combination -E

theorem surface_iff_single {b θ : ℚ} (bp : 0<b) (tn : θ≠0) :
    Surface b θ ↔ ∃ s : ℚ, s≠0 ∧ SingleFibre b θ s := by
  rw [surface_iff_conics bp tn]
  constructor
  · rintro ⟨s,z,h,j,F⟩
    exact ⟨s,F.s_ne,(conics_iff_single bp tn F.s_ne).mp ⟨z,h,j,F⟩⟩
  · rintro ⟨s,sn,H⟩
    obtain ⟨z,h,j,F⟩:=(conics_iff_single bp tn sn).mpr H
    exact ⟨s,z,h,j,F⟩

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.surface_iff_conics
#print axioms Sun28.PointLifts.conic_parameter
#print axioms Sun28.PointLifts.conics_iff_single
#print axioms Sun28.PointLifts.surface_iff_single
