import OddChart

/-! The nine independent points in Sun's ordinary and scalar certificates. -/
namespace Sun28.WitnessIndices
open ZInQ WeierstrassCurve.Affine
noncomputable section

theorem normalized_index (k : ℤ) : theta.symm (k • P) = k • genP0 := by
  rw [map_zsmul,P,theta_symm_two_smul_pointR]

theorem index_injective : Function.Injective fun k : ℤ => k • P := by
  intro k l h
  apply zsmul_genP0_injective
  exact (normalized_index k).symm.trans ((congrArg theta.symm h).trans (normalized_index l))

theorem index_of_double (A : CPoint) : ∃! k : ℤ, k • P = (2:ℕ) • A := by
  have hd : (2:ℕ) • A ∈ (nsmulAddMonoidHom (α:=CPoint) 2).range :=
    AddMonoidHom.mem_range.mpr ⟨A,rfl⟩
  rw [two_nsmul_range_C_eq_zmultiples,AddSubgroup.mem_zmultiples_iff] at hd
  obtain ⟨k,hk⟩ := hd
  exact ⟨k,hk,fun _ h => index_injective (h.trans hk.symm)⟩

structure NinePoints where
  Q : CPoint
  N : CPoint
  T : CPoint
  Z : CPoint
  H : CPoint
  U : Fin 4 → CPoint

def NinePoints.doubles (A : NinePoints) : NinePoints where
  Q := 2 • A.Q
  N := 2 • A.N
  T := 2 • A.T
  Z := 2 • A.Z
  H := 2 • A.H
  U := fun i => 2 • A.U i

def scalarPoint (w : NinePoints) (M : ℕ) : CPoint := M • w.Q

def rootPoints (w : NinePoints) (M : ℕ) : Fin 4 → CPoint :=
  ![w.N,P + scalarPoint w M,w.T,w.Z]

def translatedBase (w : NinePoints) (c : ℤ) : CPoint := w.H - c • P

def translated (w : NinePoints) (M : ℕ) (c : ℤ) (i : Fin 4) : CPoint :=
  w.U i - c • rootPoints w M i

structure Labels where
  q : ℤ
  h : ℤ
  n : Fin 4 → ℤ
  m : Fin 4 → ℤ

/-- Point equalities characterize the labels, independently of the guards. -/
structure Represents (w : NinePoints) (M : ℕ) (a : Labels) : Prop where
  q_point : a.q • P = w.Q
  h_point : a.h • P = w.H
  root_point : ∀ i, a.n i • P = rootPoints w M i
  aux_point : ∀ i, a.m i • P = w.U i

theorem Represents.unique {w M a b} (A : Represents w M a) (B : Represents w M b) : a=b := by
  have q := index_injective (A.q_point.trans B.q_point.symm)
  have h := index_injective (A.h_point.trans B.h_point.symm)
  have n := funext (fun i => index_injective ((A.root_point i).trans (B.root_point i).symm))
  have m := funext (fun i => index_injective ((A.aux_point i).trans (B.aux_point i).symm))
  cases a; cases b; congr

private theorem product_point (M : ℕ) (q : ℤ) :
    ((M:ℤ)*q) • P = M • (q • P) := by rw [← smul_smul]; rfl

theorem labels_of_doubles (A : NinePoints) (M : ℕ) :
    ∃! a : Labels, Represents A.doubles M a := by
  obtain ⟨q,hq,-⟩ := index_of_double A.Q
  obtain ⟨h,hh,-⟩ := index_of_double A.H
  obtain ⟨n,hn,-⟩ := index_of_double A.N
  obtain ⟨t,ht,-⟩ := index_of_double A.T
  obtain ⟨z,hz,-⟩ := index_of_double A.Z
  choose m hm using fun i => (index_of_double (A.U i)).exists
  let a : Labels := ⟨q,h,![n,1+(M:ℤ)*q,t,z],m⟩
  have rep : Represents A.doubles M a := by
    refine ⟨hq,hh,?_,hm⟩
    intro i
    fin_cases i
    · exact hn
    · change (1+(M:ℤ)*q) • P = P + M • ((2:ℕ) • A.Q)
      rw [add_zsmul,one_zsmul,product_point,hq]
    · exact ht
    · exact hz
  exact ⟨a,rep,fun _ other => other.unique rep⟩

/-- The group inputs from Sun §§3–4. The four other nonidentity guards in the
paper follow from these conditions and the public generator theorem. -/
structure Guards (w : NinePoints) (c : ℤ) : Prop where
  q_nonzero : w.Q ≠ 0
  h_nonzero : w.H ≠ 0
  translated_nonzero : translatedBase w c ≠ 0
  chart_N : OddChart w.N
  chart_T : OddChart w.T
  chart_Z : OddChart w.Z

/-- Indices, regularity and the multiplication equations used in the ordinary and scalar tests. -/
structure Consequences (w : NinePoints) (M : ℕ) (c : ℤ) (a : Labels) : Prop where
  represented : Represents w M a
  odd : ∀ i, Odd (a.n i)
  q_nonzero : a.q ≠ 0
  z_nonzero : a.n 3 ≠ 0
  h_nonzero : a.h ≠ 0
  base_nonzero : a.h-c ≠ 0
  anchor : a.n 1-1=(M:ℤ)*a.q
  step_ge : M ≤ (a.n 1-1).natAbs
  scalar_nonzero : a.n 1-1 ≠ 0
  scalar_point : (a.n 1-1) • P = scalarPoint w M
  base_point : (a.h-c) • P = translatedBase w c
  translated_point : ∀ i, (a.m i-c*a.n i) • P = translated w M c i
  root_nonzero : ∀ i, rootPoints w M i ≠ 0
  step_point_nonzero : scalarPoint w M ≠ 0
  scalar_cross : a.h • scalarPoint w M = (a.n 1-1) • w.H
  ordinary_cross : ∀ i, a.h • w.U i = a.m i • w.H
  translated_cross : ∀ i, (a.h-c) • translated w M c i = (a.m i-c*a.n i) • translatedBase w c

private theorem nonzero_index {k : ℤ} {A : CPoint} (e : k • P=A) (hn : A≠0) : k≠0 := by
  rintro rfl
  exact hn (e.symm.trans (zero_zsmul P))

private theorem nonzero_point {k : ℤ} (hn : k ≠ 0) : k • P ≠ 0 := by
  intro he
  exact hn (index_injective (he.trans (zero_zsmul P).symm))

private theorem commute (a b : ℤ) : a • b • P=b • a • P := by
  rw [smul_smul,smul_smul,mul_comm]

theorem derive {w : NinePoints} {M : ℕ} {c : ℤ} {a : Labels}
    (rep : Represents w M a) (guards : Guards w c) (positive : 0<M) (six : 6∣M) :
    Consequences w M c a := by
  have cyc : ((M:ℤ)*a.q) • P = scalarPoint w M := by rw [scalarPoint,product_point,rep.q_point]
  have anch : a.n 1=1+(M:ℤ)*a.q := by
    apply index_injective
    change a.n 1 • P=(1+(M:ℤ)*a.q) • P
    rw [rep.root_point,add_zsmul,one_zsmul,cyc]
    rfl
  have anchor : a.n 1-1=(M:ℤ)*a.q := by omega
  have step : (a.n 1-1) • P = scalarPoint w M := anchor ▸ cyc
  have base : (a.h-c) • P = translatedBase w c := by rw [translatedBase,sub_zsmul,rep.h_point,sub_eq_add_neg]
  have trans : ∀ i, (a.m i-c*a.n i) • P = translated w M c i := by
    intro i
    rw [translated,sub_zsmul,←smul_smul,rep.aux_point,rep.root_point,sub_eq_add_neg]
  have odds : ∀ i, Odd (a.n i) := by
    intro i
    fin_cases i
    · apply odd_of_chart; rw [rep.root_point]; exact guards.chart_N
    · obtain ⟨v,hv⟩ := six
      refine ⟨3*(v:ℤ)*a.q,?_⟩
      change a.n 1 = _
      rw [anch,hv]
      push_cast
      ring
    · apply odd_of_chart; rw [rep.root_point]; exact guards.chart_T
    · apply odd_of_chart; rw [rep.root_point]; exact guards.chart_Z
  have nr : ∀ i, a.n i ≠ 0 := fun i hi => by simpa [hi] using odds i
  have qn := nonzero_index rep.q_point guards.q_nonzero
  have hn := nonzero_index rep.h_point guards.h_nonzero
  have bn := nonzero_index base guards.translated_nonzero
  have sn : a.n 1-1≠0 := by rw [anchor]; exact mul_ne_zero (by exact_mod_cast positive.ne') qn
  have ge : M ≤ (a.n 1-1).natAbs := by
    rw [anchor,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr qn)
  refine ⟨rep,odds,qn,nr 3,hn,bn,anchor,ge,sn,step,base,trans,?_,?_,?_,?_,?_⟩
  · intro i; rw [←rep.root_point]; exact nonzero_point (nr i)
  · rw [←step]; exact nonzero_point sn
  · rw [←step,←rep.h_point]; exact commute _ _
  · intro i; rw [←rep.aux_point,←rep.h_point]; exact commute _ _
  · intro i; rw [←trans,←base]; exact commute _ _

/-- The nine inputs are actual doubles of points of the fixed elliptic curve. -/
theorem extract_from_doubles (A : NinePoints) (M : ℕ) (c : ℤ) (positive : 0<M)
    (six : 6∣M) (guards : Guards A.doubles c) :
    ∃! a : Labels, Consequences A.doubles M c a := by
  obtain ⟨a,ha,-⟩ := labels_of_doubles A M
  exact ⟨a,derive ha guards positive six,fun _ h => h.represented.unique ha⟩

#print axioms normalized_index
#print axioms index_injective
#print axioms index_of_double
#print axioms labels_of_doubles
#print axioms derive
#print axioms extract_from_doubles
end
end Sun28.WitnessIndices
