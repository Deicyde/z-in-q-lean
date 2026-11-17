import CoverTests

namespace Sun28.PointFibres
open Sun28.PointDescent Sun28.PrescribedPoints
noncomputable section

/-- The ratio of the two norm factors is prescribed as b times a square. -/
def RatioCover (b θ t : ℚ) : Prop :=
  let r := b*t^2
  ∃ a c z : ℚ, c≠0 ∧ a^2-θ*c^2=b ∧ z^2=16*b*r+(r+3)^2*θ*c^2

theorem regular_root {b θ t a c z : ℚ} (bp : 0<b) (tn : t≠0)
    (one : a^2-θ*c^2=b)
    (r : ℚ) (er : r=b*t^2) (r1 : r≠1) (r3 : r≠3) (r9 : r≠9)
    (two : z^2=16*b*r+(r+3)^2*θ*c^2) :
    ∃ L : ℚ, L≠0 ∧ (9-r)*L^2+2*((3+r)*a)*L+(1-r)*b=0 ∧
      b≠L*(3*L+2*a) ∧ b≠3*L*(L-2*a) := by
  let A := 9-r
  let B := (3+r)*a
  let C := (1-r)*b
  have an : A≠0:=sub_ne_zero.mpr (Ne.symm r9)
  have rn : r≠0:=er ▸ mul_ne_zero bp.ne' (pow_ne_zero _ tn)
  have cc : C≠0:=mul_ne_zero (sub_ne_zero.mpr (Ne.symm r1)) bp.ne'
  have discr : z^2=B^2-A*C:=by dsimp [B,A,C];linear_combination two-(r+3)^2*one
  let L := (-B+z)/A
  let M := (-B-z)/A
  have relL : A*L=(-B+z):=by unfold L;field_simp
  have relM : A*M=(-B-z):=by unfold M;field_simp
  have poly (j : ℚ) (e : A*j=(-B+z) ∨ A*j=(-B-z)) : A*j^2+2*B*j+C=0 := by
    apply mul_left_cancel₀ an
    rcases e with h|h
    · linear_combination (A*j+B+z)*h+discr
    · linear_combination (A*j+B-z)*h+discr
  have ln : L≠0:=by intro h;have v:=poly L (Or.inl relL);exact cc (by simpa [h] using v)
  have mn : M≠0:=by intro h;have v:=poly M (Or.inr relM);exact cc (by simpa [h] using v)
  have lm : A*(L*M)=C:=by
    apply mul_left_cancel₀ an
    linear_combination A*M*relL+(-B+z)*relM-discr
  have condition (j : ℚ) (p : A*j^2+2*B*j+C=0) :
      (b=j*(3*j+2*a) ∨ b=3*j*(j-2*a)) → b=r*j^2 ∨ r*b=9*j^2 := by
    dsimp [A,B,C] at p
    rintro (e|e)
    · exact Or.inl (by linear_combination (3+r)*e/4+p/4)
    · exact Or.inr (by linear_combination (3+r)*e/4-3*p/4)
  have plus : 0<r+3:=by rw [er];positivity
  have good : ¬((b=r*L^2 ∨ r*b=9*L^2) ∧ (b=r*M^2 ∨ r*b=9*M^2)) := by
    rintro ⟨x,y⟩
    have sqsum : 0<r^2-2*r+9:=by nlinarith only [sq_nonneg (r-1)]
    have eqs : A^2*(L*M)^2=C^2 :=by rw [←mul_pow,lm]
    dsimp [A,C] at eqs
    rcases x with xl|xl <;> rcases y with ym|ym
    · have h : b^2*((r-3)*(r+3)*(r^2-2*r+9))=0 := by
        linear_combination -r^2*eqs-(9-r)^2*(b*ym+r*M^2*xl)
      exact (mul_ne_zero (pow_ne_zero _ bp.ne')
        (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr r3) plus.ne') sqsum.ne')) h
    · have e : (r*b^2)*((r-3)*(r+3))=0 := by
        linear_combination (-9*r*eqs-(9-r)^2*(b*ym+9*M^2*xl))/8
      exact (mul_ne_zero (mul_ne_zero rn (pow_ne_zero _ bp.ne'))
        (mul_ne_zero (sub_ne_zero.mpr r3) plus.ne')) e
    · have e : (r*b^2)*((r-3)*(r+3))=0 := by
        linear_combination (-9*r*eqs-(9-r)^2*(b*xl+9*L^2*ym))/8
      exact (mul_ne_zero (mul_ne_zero rn (pow_ne_zero _ bp.ne'))
        (mul_ne_zero (sub_ne_zero.mpr r3) plus.ne')) e
    · have e : b^2*((r-3)*(r+3)*(r^2-18*r+9))=0 := by
        linear_combination 81*eqs+(9-r)^2*(r*b*xl+9*L^2*ym)
      have bad := (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (pow_ne_zero _ bp.ne'))).resolve_left
        (mul_ne_zero (sub_ne_zero.mpr r3) plus.ne')
      have rational : ¬IsSquare (2:ℚ):=by norm_num
      exact rational ⟨(r-9)/6,by linear_combination -bad/36⟩
  by_cases ok : b≠L*(3*L+2*a) ∧ b≠3*L*(L-2*a)
  · exact ⟨L,ln,poly L (Or.inl relL),ok⟩
  · have badL : b=L*(3*L+2*a) ∨ b=3*L*(L-2*a):=by tauto
    refine ⟨M,mn,poly M (Or.inr relM),?_⟩
    by_contra bad
    have badM : b=M*(3*M+2*a) ∨ b=3*M*(M-2*a):=by tauto
    exact good ⟨condition L (poly L (Or.inl relL)) badL,condition M (poly M (Or.inr relM)) badM⟩

theorem nonzero_of_ratio {b θ t : ℚ} (bp : 0<b) (tp : 0<θ) (tn : t≠0)
    (r1 : b*t^2≠1) (r3 : b*t^2≠3) (r9 : b*t^2≠9) (f : RatioCover b θ t) :
    NonzeroPair b θ := by
  obtain ⟨a,c,z,cn,one,two⟩:=f
  obtain ⟨L,Ln,rel,g₁,g₂⟩:=regular_root bp tn one (b*t^2) rfl r1 r3 r9 two
  let F := L^2-2*a*L+b
  have ratio : 9*L^2+6*a*L+b=(b*t^2)*F:=by dsimp [F];linear_combination rel
  have nz : F≠0:=by
    intro zero
    have G:=ratio
    rw [zero,mul_zero] at G
    dsimp [F] at zero
    have e : 12*L^2+4*b=0:=by linear_combination G+3*zero
    nlinarith only [sq_nonneg L,bp,e]
  obtain ⟨l,ln,⟨u,y,un,yn,hy⟩,⟨v,q,vn,qn,hq⟩⟩:=marked_of_norm (L:=L) (h:=b*t*F)
    bp tp.ne' cn Ln (mul_ne_zero (mul_ne_zero bp.ne' tn) nz) one
    (by rw [ratio];dsimp [F];ring)
  exact ⟨l,u,v,y,q,ln,un,vn,yn ⟨g₁,g₂⟩,qn ⟨g₁,g₂⟩,hy,hq⟩

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.regular_root
#print axioms Sun28.PointFibres.nonzero_of_ratio
