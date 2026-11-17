import MarkedCorank

namespace Sun28.Corank
open Sun28.SelmerRealization Sun28.MarkedDescent ZInQ.RouteK ZInQ.Descent
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

private theorem equal_label {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b)
    (eq : sqc (a:ℚ)=sqc (b:ℚ)) : a=b := by
  obtain ⟨v,vn,h⟩ := (sqc_eq_sqc_iff (by exact_mod_cast sa.ne_zero) (by exact_mod_cast sb.ne_zero)).mp eq
  have e := sqf_eq_of_eq_mul_sq (t:=(1:ℚ)) sa one_ne_zero (by simp : (a:ℚ)=a*1^2)
  exact e.symm.trans (sqf_eq_of_eq_mul_sq sb vn h)

/-- The two signed squarefree labels are a genuine function of the group
class modulo doubling, including the four exceptional points. -/
theorem quotient_label {l : ℕ} (pos : 0<l) {P Q : RationalPoint l}
    (e : (QuotientAddGroup.mk P : ModTwo l)=QuotientAddGroup.mk Q) :
    labels l P = labels l Q := by
  obtain ⟨B,h⟩ := QuotientAddGroup.eq_iff_sub_mem.mp e
  have p : P=Q+(B+B) := by
    change (2:ℕ) • B = P-Q at h
    rw [two_smul] at h
    rw [h]; abel
  have eq (x : ℚ) (root : x*(x-l)*(x+3*l)=0) (dn : derivativeAt l x≠0) :
      rootClass l x P=rootClass l x Q := by
    rw [p,class_add root dn,class_add root dn,SqClass.mul_self,mul_one]
  have lp : 0<(l:ℚ) := by exact_mod_cast pos
  have e1 := eq (-3*l) (by ring) (by unfold derivativeAt; nlinarith [sq_pos_of_pos lp])
  have e2 := eq l (by ring) (by unfold derivativeAt; nlinarith [sq_pos_of_pos lp])
  have e3 := (character_labels pos P).symm.trans ((Prod.ext e1 e2).trans (character_labels pos Q))
  have hp := labels_local pos P
  have hq := labels_local pos Q
  exact Prod.ext (equal_label hp.1 hq.1 (congrArg Prod.fst e3))
    (equal_label hp.2.1 hq.2.1 (congrArg Prod.snd e3))

private theorem raw_sf (a : ℤ) (sa : Squarefree a) : sqf (a:ℚ)=a :=
  sqf_eq_of_eq_mul_sq (t:=(1:ℚ)) sa one_ne_zero (by simp)

private def targetLabels : Fin 5 → ℤ×ℤ :=
  ![(1,1),(3*(n:ℤ),-(n:ℤ)),((n:ℤ),1),(3,-(n:ℤ)),(526361,1)]

private theorem labels_at_five (M : Sun28.SupportMatrix.MarkedCover 526361 n) :
    ∀ i, ∃ P : RationalPoint n, labels n P=targetLabels i := by
  have ln : 0<(n:ℚ) := by norm_num [n]
  have non : (n:ℚ) ≠ 0 := ln.ne'
  have sf : Squarefree (n:ℤ) := Int.squarefree_natCast.mpr n_shape.2.1
  have sneg : Squarefree (-(n:ℤ)) := by simpa only [←Int.squarefree_natAbs,Int.natAbs_neg,Int.natAbs_natCast] using n_shape.2.1
  have s3 : Squarefree (3:ℤ) := Int.squarefree_natCast.mpr (by decide : Nat.Prime 3).squarefree
  have s3n : Squarefree (3*(n:ℤ)) := by
    have sn : Squarefree (3*n) := Nat.squarefree_mul_iff.mpr
      ⟨by decide,(by decide : Nat.Prime 3).squarefree,n_shape.2.1⟩
    exact_mod_cast Int.squarefree_natCast.mpr sn
  have s1 : Squarefree (1:ℤ) := squarefree_one
  have sB : Squarefree (526361:ℤ) := Sun28.FixedLocalRows.fixed_descent.2.1
  have r0 : (0:ℚ)* (0-n)*(0+3*n)=0 := by ring
  have r1 : (n:ℚ)* (n-n)*(n+3*n)=0 := by ring
  have rm : (-3*(n:ℚ))* (-3*n-n)*(-3*n+3*n)=0 := by ring
  have d0 : derivativeAt n 0≠0 := by norm_num [derivativeAt,n]
  have d1 : derivativeAt n n≠0 := by norm_num [derivativeAt,n]
  have dm : derivativeAt n (-3*n)≠0 := by norm_num [derivativeAt,n]
  have nm : (-3*(n:ℚ))≠0 := by linarith
  have neq : (-3*(n:ℚ))≠n := by linarith
  intro i
  fin_cases i
  · refine ⟨0,?_⟩
    exact Prod.ext (raw_sf 1 s1) (raw_sf 1 s1)
  · refine ⟨rootPoint r0 d0,?_⟩
    change (sqf _,sqf _) = (3*(n:ℤ),-(n:ℤ))
    simp only [rootPoint,raw,↓reduceIte]
    exact Prod.ext (by simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using raw_sf _ s3n)
      (by simpa only [Int.cast_neg,Int.cast_natCast] using raw_sf _ sneg)
  · refine ⟨rootPoint r1 d1,?_⟩
    change (sqf _,sqf _) = ((n:ℤ),1)
    simp only [rootPoint,raw,ite_eq_right non,↓reduceIte]
    exact Prod.ext (by simpa only [Int.cast_natCast] using raw_sf _ sf) (raw_sf 1 s1)
  · refine ⟨rootPoint rm dm,?_⟩
    change (sqf _,sqf _) = (3,-(n:ℤ))
    simp only [rootPoint,raw,ite_eq_right nm,ite_eq_right neq,↓reduceIte]
    exact Prod.ext (raw_sf 3 s3) (by simpa only [Int.cast_neg,Int.cast_natCast] using raw_sf _ sneg)
  · obtain ⟨u,v,w,un,vn,wn,h1,h2⟩ :=
      Sun28.SupportMatrix.cover_affine (by norm_num) ln (by norm_num) (by norm_num [n]) M
    let x : ℚ := 526361*u^2
    let y : ℚ := 526361*u*v*w
    have yy : y≠0 := by dsimp [y]; positivity
    have xx : x≠0 := by dsimp [x]; positivity
    have xu : x≠(n:ℚ) := by
      intro h
      change x-n=v^2 at h1
      rw [h,sub_self] at h1
      exact vn (by nlinarith)
    have xv : x≠ -3*(n:ℚ) := by
      dsimp [x]
      nlinarith [sq_nonneg u]
    have eq : y^2=x*(x-n)*(x+3*n) := by
      change x-n=v^2 at h1; change x+3*n=526361*w^2 at h2
      rw [h1,h2]; dsimp [x,y]; ring
    have ns : (twistCurve n).toAffine.Nonsingular x y := by
      rw [nonsingular_iff]; refine ⟨equation.mpr eq, Or.inr ?_⟩
      simp only [twistCurve, WeierstrassCurve.toAffine,zero_mul,sub_zero]
      exact fun h => yy (by linarith)
    refine ⟨.some x y ns,?_⟩
    change (sqf _,sqf _) = (526361,1)
    simp only [raw,ite_eq_right xx,ite_eq_right xu,ite_eq_right xv]
    exact Prod.ext (sqf_eq_of_eq_mul_sq sB wn h2)
      (sqf_eq_of_eq_mul_sq s1 vn (by simpa only [Int.cast_one,one_mul] using h1))

/-- A rational point on this literal cover gives a fifth class modulo
doubling, in addition to the four classes of rational two-torsion. -/
theorem fifth_class (M : Sun28.SupportMatrix.MarkedCover 526361 n) :
    Nonempty (Fin 5 ↪ ModTwo n) := by
  classical
  choose pt row using labels_at_five M
  have inj : Function.Injective targetLabels := by decide +kernel
  refine ⟨⟨fun i => QuotientAddGroup.mk (pt i),fun i j e => inj ?_⟩⟩
  rw [←row i,←row j]
  exact quotient_label (by decide : 0<n) e

theorem cover_iff_infinite [AddGroup.FG (RationalPoint n)] :
    Sun28.SupportMatrix.MarkedCover 526361 n ↔ ∃ P : RationalPoint n, ¬ IsOfFinAddOrder P := by
  constructor
  · intro M
    by_contra! h
    obtain ⟨r,T,_,tfin,⟨f⟩⟩ := split_finitely_generated (RationalPoint n)
    have rz : r=0 := by
      by_contra non
      let i : Fin r := ⟨0,Nat.pos_of_ne_zero non⟩
      let v : Fin r → ℤ := fun _ => 1
      obtain ⟨j,jpos,hz⟩ := (h (f.symm (v,0))).exists_nsmul_eq_zero
      have e := congrArg (fun a => (f a).1 i) hz
      simp [map_nsmul,v] at e
      omega
    have sz := quotient_growth f (by decide : 2≠0)
    rw [four_torsion (by decide : 0<n),rz] at sz
    change Nat.card (ModTwo n)=_ at sz
    have : Finite (ModTwo n) := Nat.finite_of_card_ne_zero (by rw [sz];decide)
    obtain ⟨J⟩ := fifth_class M
    have bound := Nat.card_le_card_of_injective J J.injective
    rw [Nat.card_fin,sz] at bound
    omega
  · exact fun p => marked_of_descent (by decide) (kummer_separation (by decide))
      (eight_of_infinite_point (by decide) p) Sun28.FixedLocalRows.fixed_descent

theorem fixed_cover_iff_sha [AddGroup.FG (RationalPoint n)] (K : PrimaryData (RationalPoint n))
    (comparison : LocalComparison n K) :
    Sun28.SupportMatrix.MarkedCover 526361 n ↔ K.d=0 := by
  constructor
  · intro m
    exact (eight_rational_iff (by decide) K comparison Sun28.FixedLocalRows.local_class_count).mp
      (eight_of_infinite_point (by decide) (cover_iff_infinite.mp m))
  · intro d
    apply marked_of_descent (by decide) (kummer_separation (by decide)) _ Sun28.FixedLocalRows.fixed_descent
    exact (eight_rational_iff (by decide) K comparison Sun28.FixedLocalRows.local_class_count).mpr d

end
end Sun28.Corank

#print axioms Sun28.Corank.quotient_label
#print axioms Sun28.Corank.fifth_class
#print axioms Sun28.Corank.cover_iff_infinite
#print axioms Sun28.Corank.fixed_cover_iff_sha
