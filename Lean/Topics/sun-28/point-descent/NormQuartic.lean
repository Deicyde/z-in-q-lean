import QuadraticChord

namespace Sun28.PointDescent
open TwistExtension

def NormQuartic (b θ : ℚ) : Prop := ∃ a c L h : ℚ,
  c≠0 ∧ L≠0 ∧ h≠0 ∧ a^2-θ*c^2=b ∧
  h^2=b*(L^2-2*a*L+b)*(9*L^2+6*a*L+b)

/-- The product of three quadratic norms supplies the norm of the ordinate squared. -/
theorem norm_polynomial (a k L : ℚ) :
    (realPart a k L)^2-k*(linearPart a k L)^2=
    (a^2-k)*(L^2-2*a*L+(a^2-k))*(9*L^2+6*a*L+(a^2-k)) := by
  unfold realPart linearPart
  ring

/-- A rational scalar makes an element with nonzero square norm a square. -/
theorem rational_rescaling {A d θ h : ℚ} (hn : h≠0) (H : A^2-θ*d^2=h^2) :
    ∃ s e f : ℚ, s≠0 ∧ e^2+θ*f^2=s*A ∧ 2*e*f=s*d := by
  have step (j : ℚ) (j2 : j^2=h^2) (nj : A+j≠0) :
      ∃ s e f : ℚ, s≠0 ∧ e^2+θ*f^2=s*A ∧ 2*e*f=s*d := by
    exact ⟨2*(A+j),A+j,d,mul_ne_zero (by norm_num) nj,
      by linear_combination j2-H,by ring⟩
  by_cases k : A+h=0
  · exact step (-h) (by ring) (by intro z;apply hn;linear_combination (k-z)/2)
  · exact step h rfl k

theorem marked_of_norm {b θ a c L h : ℚ} (bp : 0<b) (tn : θ≠0)
    (cn : c≠0) (Ln : L≠0) (hn : h≠0) (norm : a^2-θ*c^2=b)
    (square : h^2=b*(L^2-2*a*L+b)*(9*L^2+6*a*L+b)) :
    let regular := b≠L*(3*L+2*a) ∧ b≠3*L*(L-2*a)
    ∃ l : ℚ, l≠0 ∧ MarkedPoint b l regular ∧ MarkedPoint b (l*θ) regular := by
  let k := θ*c^2
  have H := norm_polynomial a k L
  change a^2-k=b at norm
  rw [norm,←square] at H
  obtain ⟨s,e,f,sn,Hr,Hi⟩:=rational_rescaling hn (A:=realPart a k L)
    (d:=c*linearPart a k L) (θ:=θ) (by dsimp [k] at H ⊢;linear_combination H)
  have HH : (s*a)^2-θ*(s*c)^2=b*s^2:=by dsimp [k] at norm;linear_combination s^2*norm
  have rr := quadratic_marked_pair (a:=s*a) (c:=s*c) (d:=s*e) (e:=s*f) (s:=s) (l:=s*L)
    bp tn (mul_ne_zero sn cn) sn HH
    (by unfold realPart at Hr ⊢;dsimp [k] at Hr;linear_combination s^2*Hr)
    (by unfold linearPart at Hi ⊢;dsimp [k] at Hi;linear_combination s^2*Hi)
  obtain ⟨⟨u,y,un,yn,hy⟩,⟨v,z,vn,zn,hz⟩⟩ := rr
  have regular (H₀ : b≠L*(3*L+2*a) ∧ b≠3*L*(L-2*a)) :
      (s*a)^2-θ*(s*c)^2≠s*L*(3*(s*L)+2*(s*a)) ∧
      (s*a)^2-θ*(s*c)^2≠3*(s*L)*(s*L-2*(s*a)) := by
    constructor
    · intro eq;apply H₀.1;apply mul_right_cancel₀ (pow_ne_zero 2 sn);linear_combination eq-HH
    · intro eq;apply H₀.2;apply mul_right_cancel₀ (pow_ne_zero 2 sn);linear_combination eq-HH
  exact ⟨s*L,mul_ne_zero sn Ln,⟨u,y,un,fun ex=>yn (regular ex),hy⟩,v,z,vn,fun ex=>zn (regular ex),hz⟩

theorem surface_of_norm_quartic {b θ : ℚ} (bp : 0<b) (tn : θ≠0)
    (w : NormQuartic b θ) : Surface b θ := by
  obtain ⟨_,_,_,_,cn,Ln,hn,norm,square⟩:=w
  obtain ⟨l,ln,⟨u,y,un,_,hy⟩,⟨v,z,vn,_,hz⟩⟩:=marked_of_norm bp tn cn Ln hn norm square
  exact (surface_iff_pair bp tn).mpr ⟨l,ln,⟨u,y,un,hy⟩,v,z,vn,hz⟩

/-- With L=-2a/3 the second norm returns to b; the other is a single split conic. -/
theorem norm_quartic_of_two_conics {b θ a c z : ℚ} (bp : 0<b) (tp : 0<θ) (cn : c≠0)
    (one : a^2-θ*c^2=b) (two : z^2=b+16*a^2/9) : NormQuartic b θ := by
  have an : a≠0:=by rintro rfl; nlinarith [mul_pos tp (sq_pos_of_ne_zero cn)]
  have zn : z≠0:=by rintro rfl; nlinarith [sq_nonneg a]
  exact ⟨a,c,-2*a/3,b*z,cn,div_ne_zero (mul_ne_zero (by norm_num) an) (by norm_num),
    mul_ne_zero bp.ne' zn,one,by linear_combination b^2*two⟩

def AuxiliaryCover (b θ : ℚ) : Prop := ∃ k w : ℚ,
  k≠0 ∧ w≠0 ∧ θ*w^2=(k^2-b)*(k^2-81*b)

/-- A single fixed elliptic two-cover gives both of Sun's points. -/
theorem norm_quartic_of_auxiliary {b θ : ℚ} (bp : 0<b) (tp : 0<θ)
    (cov : AuxiliaryCover b θ) : NormQuartic b θ := by
  obtain ⟨k,w,kn,wn,H⟩:=cov
  apply norm_quartic_of_two_conics (a:=(k^2-9*b)/(8*k)) (c:=w/(8*k))
    (z:=(k^2+9*b)/(6*k)) bp tp (div_ne_zero wn (mul_ne_zero (by norm_num) kn))
  · field_simp
    linear_combination -H
  · field_simp
    ring

end Sun28.PointDescent
#print axioms Sun28.PointDescent.norm_polynomial
#print axioms Sun28.PointDescent.rational_rescaling
#print axioms Sun28.PointDescent.marked_of_norm
#print axioms Sun28.PointDescent.surface_of_norm_quartic
#print axioms Sun28.PointDescent.norm_quartic_of_two_conics
#print axioms Sun28.PointDescent.norm_quartic_of_auxiliary
