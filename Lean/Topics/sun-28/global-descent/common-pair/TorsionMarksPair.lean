import TwiceSigned
import FixedTwistCover

/-! On a variable positive twist, translation by rational two-torsion interchanges the two factors of its parameter as marked classes. -/
namespace Sun28.CommonPair
open Sun28.PairedClasses Sun28.PrescribedPoints Sun28.PreparedPoles Sun28.TwistExtension
  Sun28.GlobalDescent
noncomputable section

/-- Translation by (r,0) fixes the curve y²=x(x-r)(x+3r). -/
def shift (r : ℚ) (P : ℚ×ℚ) : ℚ×ℚ :=
  (r*(P.1+3*r)/(P.1-r), -4*r^2*P.2/(P.1-r)^2)

theorem shifted_curve {r x y : ℚ} (h:y^2=x*(x-r)*(x+3*r)) (nx:x-r≠0) :
    let Q:=shift r (x,y)
    Q.2^2=Q.1*(Q.1-r)*(Q.1+3*r) := by
  dsimp [shift]
  field_simp [nx]
  linear_combination 16*r^4*h

/-- Translation by (r,0) and (-3r,0), respectively, on the complement of two-torsion.
The formula for the complementary square root uses the nonzero old ordinate. -/
def shiftNegative (r : ℚ) (P : ℚ×ℚ) : ℚ×ℚ :=
  (-3*r*(P.1-r)/(P.1+3*r), -12*r^2*P.2/(P.1+3*r)^2)

theorem shifted_negative_curve {r x y : ℚ} (h:y^2=x*(x-r)*(x+3*r)) (nx:x+3*r≠0) :
    let Q:=shiftNegative r (x,y)
    Q.2^2=Q.1*(Q.1-r)*(Q.1+3*r) := by
  let z:=-3*r*(x-r)/(x+3*r)
  have a : z-r=-4*r*x/(x+3*r) := by dsimp [z];field_simp [nx];ring
  have b : z+3*r=12*r^2/(x+3*r) := by dsimp [z];field_simp [nx];ring
  change (-12*r^2*y/(x+3*r)^2)^2=z*(z-r)*(z+3*r)
  rw [a,b,div_pow,mul_pow,h]
  dsimp [z]
  have normal : x+r*3≠0 := by simpa only [mul_comm 3 r] using nx
  field_simp [nx,normal]
  ring

def Strict (b l : ℚ) : Prop := ∃u y : ℚ, u≠0 ∧ y≠0 ∧
    y^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l)

theorem complementary_strict {b d k:ℚ} (bp:0<b) (dp:0<d) (sign:k=1 ∨ k=-3) :
    Strict b (k*b*d) → Strict d (k*b*d) := by
  rintro ⟨u,y,un,yn,h⟩
  let r:=k*b*d
  let x:=b*u^2
  have kn:k≠0:=by rcases sign with rfl|rfl <;> norm_num
  have rn:r≠0:=mul_ne_zero (mul_ne_zero kn bp.ne') dp.ne'
  change y^2=x*(x-r)*(x+3*r) at h
  have nonzero : x*(x-r)*(x+3*r)≠0:=h ▸ pow_ne_zero 2 yn
  have dn := right_ne_zero_of_mul (left_ne_zero_of_mul nonzero)
  have pn := right_ne_zero_of_mul nonzero
  rcases sign with rfl|rfl
  · let v:=y/(u*(x-r))
    have mark : (shift r (x,y)).1=d*v^2 := by
      dsimp [shift,v]
      field_simp [dn,un]
      dsimp [r,x] at *
      linear_combination -d*h
    have sz := shifted_curve h dn
    dsimp only at sz
    rw [mark] at sz
    exact ⟨v,(shift r (x,y)).2,div_ne_zero yn (mul_ne_zero un dn),
      div_ne_zero (by exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 rn)) yn) (pow_ne_zero 2 dn),sz⟩
  · let v:=3*y/(u*(x+3*r))
    have mark : (shiftNegative r (x,y)).1=d*v^2 := by
      dsimp [shiftNegative,v]
      field_simp [pn,un]
      dsimp [r,x] at *
      linear_combination -3*d*h
    have sz := shifted_negative_curve h pn
    dsimp only at sz
    rw [mark] at sz
    exact ⟨v,(shiftNegative r (x,y)).2,div_ne_zero (mul_ne_zero (by norm_num) yn) (mul_ne_zero un pn),
      div_ne_zero (by exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 rn)) yn) (pow_ne_zero 2 pn),sz⟩

theorem complementary_iff {b d k:ℚ} (bp:0<b) (dp:0<d) (sign:k=1 ∨ k=-3) :
    Strict b (k*b*d) ↔ Strict d (k*b*d) := by
  refine ⟨complementary_strict bp dp sign,?_⟩
  rw [show k*b*d=k*d*b by ring]
  exact complementary_strict dp bp sign

/-- For n=bq the fixed common positive twists exchange their abscissa tests
for two complementary marks, q and qθ, at the same two levels. -/
theorem fixed_pair_iff {b q θ:ℚ} (bpos:0<b) (qpos:0<q) (tpos:0<θ) :
    (Strict b (b*q) ∧ Strict b (b*q*θ)) ↔
      (Strict q (b*q) ∧ Strict (q*θ) (b*q*θ)) := by
  have one:=complementary_iff (k:=1) bpos qpos (Or.inl rfl)
  have two:=complementary_iff (k:=1) bpos (mul_pos qpos tpos) (Or.inl rfl)
  simpa only [one_mul,←mul_assoc] using and_congr one two

theorem nonzero_of_complementary {b q θ:ℚ} (bpos:0<b) (qpos:0<q) (tpos:0<θ)
    (one:Strict q (b*q)) (two:Strict (q*θ) (b*q*θ)) : NonzeroPair b θ := by
  obtain ⟨⟨u,y,un,yn,p⟩,v,z,vn,zn,j⟩:=(fixed_pair_iff bpos qpos tpos).mpr ⟨one,two⟩
  exact ⟨b*q,u,v,y,z,(mul_pos bpos qpos).ne',un,vn,yn,zn,p,j⟩

end
end Sun28.CommonPair
#print axioms Sun28.CommonPair.shifted_curve
#print axioms Sun28.CommonPair.shifted_negative_curve
#print axioms Sun28.CommonPair.complementary_strict
#print axioms Sun28.CommonPair.complementary_iff
#print axioms Sun28.CommonPair.fixed_pair_iff
#print axioms Sun28.CommonPair.nonzero_of_complementary
