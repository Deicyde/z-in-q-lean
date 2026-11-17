import SparseTruncation

namespace Sun28.Ordinary
open Sun28.Scalar

/-- When two full logarithms A,B satisfy hA=mB and the degree-k remainders
have k extra digits at their own depths, denominator clearing keeps all k
digits even if m/h is not integral. -/
private theorem relative_field_ratio {L : Type*} [Field L] (v : AddValuation L (WithTop ℤ))
    {h m A B X Y : L} {H M a b k : ℤ} (hk : 0<k)
    (vh : v h=(H:WithTop ℤ)) (vm : v m=(M:WithTop ℤ))
    (va : v A=(a:WithTop ℤ)) (vb : v B=(b:WithTop ℤ))
    (ax : ((a+k:ℤ):WithTop ℤ)≤v (A-X)) (by' : ((b+k:ℤ):WithTop ℤ)≤v (B-Y))
    (cross : h*A=m*B) :
    Y≠0 ∧ v (X/Y)=v (m/h) ∧ ((M+k:ℤ):WithTop ℤ)≤v (h*(X/Y)-m) := by
  have vx := trunc_order v va hk ax
  have vy := trunc_order v vb hk by'
  have yn : Y≠0 := by rintro rfl; rw [v.map_zero] at vy; exact WithTop.top_ne_coe vy
  have eq := congrArg v cross
  rw [v.map_mul,v.map_mul,vh,vm,va,vb,←WithTop.coe_add,←WithTop.coe_add] at eq
  have sum : H+a=M+b := WithTop.coe_inj.mp eq
  have vl : v (X/Y)=v (m/h) := by
    rw [v.map_div,v.map_div,vx,vy,vm,vh]
    exact WithTop.coe_inj.mpr (by omega)
  refine ⟨yn,vl,?_⟩
  have first : ((M+b+k:ℤ):WithTop ℤ) ≤ v (h*(A-X)) := by
    rw [v.map_mul,vh]
    calc
      _ ≤ ((H+(a+k):ℤ):WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
      _ ≤ _ := by rw [WithTop.coe_add]; exact add_le_add le_rfl ax
  have second : ((M+b+k:ℤ):WithTop ℤ) ≤ v (m*(B-Y)) := by
    rw [v.map_mul,vm]
    calc
      _ ≤ ((M+(b+k):ℤ):WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
      _ ≤ _ := by rw [WithTop.coe_add]; exact add_le_add le_rfl by'
  have numer : h*X-m*Y = m*(B-Y)-h*(A-X) := by linear_combination cross
  have bound : ((M+b+k:ℤ):WithTop ℤ)≤v (h*X-m*Y) := numer ▸ v.map_le_sub second first
  have clear : h*(X/Y)-m=(h*X-m*Y)/Y := by field_simp
  rw [clear,v.map_div,vy,sub_eq_add_neg]
  calc
    _ = ((M+b+k:ℤ):WithTop ℤ)+(-(b:WithTop ℤ)) := by norm_cast; ring
    _ ≤ _ := add_le_add bound le_rfl

theorem nonzero_field_ratio {L : Type*} [Field L] [CharZero L] (v : AddValuation L (WithTop ℤ))
    {h m A B X Y : L} {H M a b k : ℤ} (hk : 0<k)
    (vh : v h=(H:WithTop ℤ)) (vm : v m=(M:WithTop ℤ))
    (va : v A=(a:WithTop ℤ)) (vb : v B=(b:WithTop ℤ))
    (ax : ((a+k:ℤ):WithTop ℤ)≤v (A-X)) (by' : ((b+k:ℤ):WithTop ℤ)≤v (B-Y))
    (cross : h*A=m*B) : Y≠0 ∧ v (X/Y)=v (m/h) ∧ v (m/h)+(k:WithTop ℤ) ≤ v (X/Y-m/h) := by
  obtain ⟨yn,eq,prec⟩ := relative_field_ratio v hk vh vm va vb ax by' cross
  have hn : h≠0 := by rintro rfl; rw [v.map_zero] at vh; exact WithTop.top_ne_coe vh
  have same : X/Y-m/h = (h*(X/Y)-m)/h := by field_simp
  refine ⟨yn,eq,?_⟩
  rw [same,v.map_div (x:=h*(X/Y)-m),v.map_div,vm,vh]
  rw [sub_eq_add_neg,sub_eq_add_neg]
  calc
    _ = ((M+k:ℤ):WithTop ℤ)+(-(H:WithTop ℤ)) := by norm_cast; ring
    _ ≤ _ := add_le_add prec le_rfl

end Sun28.Ordinary
#print axioms Sun28.Ordinary.nonzero_field_ratio
