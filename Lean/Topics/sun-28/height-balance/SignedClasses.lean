import PairedUnits

/-! A test in terms of the signed squarefree part of the actual integer rows. -/
namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.MinimalConductors Sun28.HeightFibres ZInQ.RouteK
noncomputable section

private theorem class_of_common {a d u:ℤ} (nz:a≠0) (h:a=d*u^2) : sqfInt a=sqfInt d := by
  have dn:d≠0:=fun z=>nz (by simp [h,z])
  have un:u≠0:=fun z=>nz (by simp [h,z])
  rw [h,sqfInt_mul_sq dn un]

theorem four_classes (R : FourRows) {A B:ℤ} (off:∀ i,oldForm i A B≠0) :
    (∃ d u v w,R.Balance A B d u v w) ↔
    let x:=sqfInt (R.weightA*oldForm R.a A B)
    let y:=sqfInt (R.weightB*oldForm R.b A B)
    let z:=sqfInt (R.weightC*oldForm R.c A B)
    x=y ∧ x=z := by
  let x:=R.weightA*oldForm R.a A B
  let y:=R.weightB*oldForm R.b A B
  let z:=R.weightC*oldForm R.c A B
  have xn:x≠0:=mul_ne_zero (mul_ne_zero (det_ne R.ib) (det_ne R.ic)) (off _)
  have yn:y≠0:=mul_ne_zero (mul_ne_zero (det_ne R.ia) (det_ne R.ic)) (off _)
  have zn:z≠0:=mul_ne_zero (mul_ne_zero (det_ne R.ia) (det_ne R.ib)) (off _)
  change _ ↔ sqfInt x = sqfInt y ∧ sqfInt x = sqfInt z
  constructor
  · rintro ⟨d,u,v,w,h⟩
    rw [class_of_common xn h.first,class_of_common yn h.second,class_of_common zn h.third]
    exact ⟨rfl,rfl⟩
  · rintro ⟨xy,xz⟩
    obtain ⟨_,u,_,a⟩:=sqfInt_spec xn
    obtain ⟨_,v,_,b⟩:=sqfInt_spec yn
    obtain ⟨_,w,_,c⟩:=sqfInt_spec zn
    exact ⟨sqfInt x,u,v,w,a,xy.symm ▸ b,xz.symm ▸ c⟩

theorem three_classes (R : ThreeRows) {A B:ℤ} (off:∀ i,oldForm i A B≠0) :
    (∃ d u v,R.Match A B d u v) ↔
      sqfInt (det R.center R.b*oldForm R.a A B)=sqfInt (det R.center R.a*oldForm R.b A B) := by
  let x:=det R.center R.b*oldForm R.a A B
  let y:=det R.center R.a*oldForm R.b A B
  have xn:x≠0:=mul_ne_zero (det_ne R.ib) (off _)
  have yn:y≠0:=mul_ne_zero (det_ne R.ia) (off _)
  change _ ↔ sqfInt x=sqfInt y
  constructor
  · rintro ⟨d,u,v,h⟩
    exact (class_of_common xn h.first).trans (class_of_common yn h.second).symm
  · intro xy
    obtain ⟨_,u,_,a⟩:=sqfInt_spec xn
    obtain ⟨_,v,_,b⟩:=sqfInt_spec yn
    exact ⟨sqfInt x,u,v,a,xy.symm ▸ b⟩

/-- Each omission of one of the five marks has its own absolute Legendre invariant. -/
def legendre (q:ℚ) : ℚ := 256*(1-q+q^2)^3/(q^2*(1-q)^2)
def branchCross (a b c e:Fin 5) : ℚ := (det a c*det b e:ℚ)/(det a e*det b c:ℚ)
def omission (i:Fin 5) : Fin 4→Fin 5 :=
  ![![1,2,3,4],![0,2,3,4],![0,1,3,4],![0,1,2,4],![0,1,2,3]] i

theorem four_point_invariants :
    Function.Injective (fun i : Fin 5=> let t:=omission i; legendre (branchCross (t 0) (t 1) (t 2) (t 3))) := by
  let jj (i:Fin 5):=legendre (branchCross (omission i 0) (omission i 1) (omission i 2) (omission i 3))
  let values:Fin 5→ℚ:=![1439069689/44100,1169975873419524361/108425318400,128031684631201/9922500,
    2179252305146449/66177562500,191342053882402567201/129708022500]
  have calc' (i:Fin 5):jj i=values i:=by
    fin_cases i <;> norm_num [jj,legendre,branchCross,omission,det,coeffA,coeffB,values,Matrix.cons_val_fin_one,Matrix.cons_val_zero,Matrix.cons_val_succ]
  intro i j h
  change jj i=jj j at h
  rw [calc',calc'] at h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [values,Matrix.cons_val_fin_one,Matrix.cons_val_zero,Matrix.cons_val_succ] at h

end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.four_classes
#print axioms Sun28.HeightBalance.three_classes
#print axioms Sun28.HeightBalance.four_point_invariants
