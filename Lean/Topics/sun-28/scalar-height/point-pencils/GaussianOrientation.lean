import PrimitiveCircle

/-! A represented scalar norm has just one orientation up to the four
Gaussian units; in particular the shorter normalized leg is intrinsic. -/
namespace Sun28.PointPencils

theorem same_orientation (x : ℚ) {d w W : ℕ} {u v p c U V P C : ℤ}
    (e : Circle x d w u v p c) (f : Circle x d W U V P C) :
    ∃ h k : ℤ, h^2+k^2=1 ∧ U=u*h-v*k ∧ V=v*h+u*k ∧ p=h*P-k*C ∧ c=k*P+h*C := by
  let a:=x.num
  let b:ℤ:=x.den
  let L:=u*U+v*V
  let M:=u*V-v*U
  let D:ℤ:=d
  have dn:D≠0:=by dsimp [D];exact_mod_cast e.squarefree.ne_zero
  have ab:D ∣ U*a+V*b := by refine ⟨P,?_⟩;dsimp [a,b,D];rw [f.point.1,f.point.2,←f.seed];ring
  have ba:D ∣ U*b-V*a := by refine ⟨C,?_⟩;dsimp [a,b,D];rw [f.point.1,f.point.2,←f.seed];ring
  obtain ⟨j,ej⟩:=ab
  obtain ⟨l,el⟩:=ba
  have norm : u^2+v^2=D:=e.seed
  -- Use the primitive *original* coordinates: b is a unit at D.
  have db : IsCoprime D b := by
    have cop : IsCoprime a b:=Int.isCoprime_iff_gcd_eq_one.mpr
      (by simpa only [a,b,Int.gcd_def,Int.natAbs_natCast] using x.reduced.gcd_eq_one)
    have normAB : D ∣ a^2+b^2 := by
      refine ⟨p^2+c^2,?_⟩
      dsimp only [a,b];rw [e.point.1,e.point.2,←norm];ring
    have hb := (show IsCoprime (a^2) b from cop.pow_left).add_mul_left_left b
    exact (show IsCoprime (a^2+b^2) b by simpa only [←sq b] using hb).of_isCoprime_of_dvd_left normAB
  have hL : D ∣ L := by
    apply db.dvd_of_dvd_mul_right
    refine ⟨U*c+v*j,?_⟩
    dsimp only [L]
    have en : u*b-v*a=D*c := by
      dsimp only [a,b];rw [e.point.1,e.point.2,←norm];ring
    linear_combination U*en+v*ej
  have hM : D ∣ M := by
    apply db.dvd_of_dvd_mul_right
    refine ⟨V*c-v*l,?_⟩
    dsimp only [M]
    have en : u*b-v*a=D*c := by
      dsimp only [a,b];rw [e.point.1,e.point.2,←norm];ring
    linear_combination V*en-v*el
  obtain ⟨h,eh⟩:=hL
  obtain ⟨k,ek⟩:=hM
  dsimp only [L] at eh;dsimp only [M] at ek
  have ors : U=u*h-v*k ∧ V=v*h+u*k := by
    constructor <;> apply mul_left_cancel₀ dn
    · linear_combination u*eh-v*ek-U*norm
    · linear_combination v*eh+u*ek-V*norm
  have ns := f.seed
  change U^2+V^2=D at ns
  rw [ors.1,ors.2] at ns
  have unit:h^2+k^2=1:=by
    apply mul_left_cancel₀ dn
    linear_combination ns-(h^2+k^2)*norm
  have eqp:=e.point.1.symm.trans f.point.1
  have eqc:=e.point.2.symm.trans f.point.2
  rw [ors.1,ors.2] at eqp eqc
  refine ⟨h,k,unit,ors.1,ors.2,?_,?_⟩ <;> apply mul_left_cancel₀ dn
  · linear_combination u*eqp+v*eqc-(p-h*P+k*C)*norm
  · linear_combination -v*eqp+u*eqc-(c-k*P-h*C)*norm

theorem shorter_leg_unique (x : ℚ) {d w W : ℕ} {u v p c U V P C : ℤ}
    (e : Circle x d w u v p c) (f : Circle x d W U V P C) :
    min |p| |c|=min |P| |C| := by
  obtain ⟨h,k,unit,_,_,hp,hc⟩:=same_orientation x e f
  have hh : -1≤h ∧ h≤1 := by constructor <;> nlinarith only [unit,sq_nonneg k,sq_nonneg (h-1),sq_nonneg (h+1)]
  have hk : -1≤k ∧ k≤1 := by constructor <;> nlinarith only [unit,sq_nonneg h,sq_nonneg (k-1),sq_nonneg (k+1)]
  obtain ⟨_,_⟩:=hh;obtain ⟨_,_⟩:=hk
  rw [hp,hc]
  interval_cases h <;> interval_cases k
  all_goals try norm_num at unit
  all_goals simp only [Int.reduceNeg,neg_one_mul,one_mul,zero_mul,sub_zero,add_zero,zero_add,zero_sub,abs_neg,neg_neg]
  all_goals exact min_comm ..

end Sun28.PointPencils
#print axioms Sun28.PointPencils.same_orientation
#print axioms Sun28.PointPencils.shorter_leg_unique
