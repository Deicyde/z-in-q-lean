import PhysicalIndexResidues
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

namespace Candidate80
open EllipticOrbit.Field
open EllipticOrbit.SignedLabels
open WeierstrassCurve.Affine
open EllipticHeight.Labels
open ProjectionFibres ProjectionFibres.Actual

/-- The local version of the doubled-range assertion on C, the curve of this circuit. -/
def DoubledRange : Prop :=
  (nsmulAddMonoidHom (α:=Point) 2).range=AddSubgroup.zmultiples P

private theorem twiceT : (2:ℕ) • T=0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [negY]; simp
private theorem twiceU : (2:ℕ) • U=0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [negY]; simp

/-- The third affine point of order two lies on the horizontal chord through T and U. -/
theorem torsion_sum : coordinates (T+U)=some (-delta,0) := by
  have dx : (0:K)≠delta := by decide +kernel
  rw [T,U,WeierstrassCurve.Affine.Point.add_of_X_ne dx]
  change some (E.toAffine.addX 0 delta (E.toAffine.slope 0 delta 0 0),
    E.toAffine.addY 0 delta 0 (E.toAffine.slope 0 delta 0 0))=_
  rw [slope_of_X_ne dx,sub_self,zero_div]
  decide +kernel

/-- The kernel of multiplication by two, with all four points explicitly identified. -/
theorem two_torsion (Q : Point) : (2:ℕ) • Q=0 ↔ Q=0 ∨ Q=T ∨ Q=U ∨ Q=T+U := by
  constructor
  · intro kill
    cases Q with
    | zero => exact Or.inl rfl
    | @some x y ns =>
      have fixed : (WeierstrassCurve.Affine.Point.some ns : Point)=
          -(WeierstrassCurve.Affine.Point.some ns : Point) :=
        eq_neg_of_add_eq_zero_left (by simpa only [two_nsmul] using kill)
      have eq:=congrArg coordinates fixed
      rw [WeierstrassCurve.Affine.Point.neg_some] at eq
      change some (x,y)=some (x,E.toAffine.negY x y) at eq
      have yy:=congrArg Prod.snd (Option.some.inj eq)
      change y=E.toAffine.negY x y at yy
      rw [negY] at yy
      have yz : y=0 := by linear_combination yy/2
      have curve:=(equation x y).mp ns.1
      have factor : x*(x-delta)*(x+delta)=0 := by
        calc _ = x^3-D*x := by rw [←delta_sq]; ring
             _ = 0 := by rw [←curve,yz]; ring
      rcases mul_eq_zero.mp factor with left|right
      · rcases mul_eq_zero.mp left with x0|xd
        · right; left; apply coordinates_injective
          change some (x,y)=some (0,0); rw [x0,yz]
        · right; right; left; apply coordinates_injective
          change some (x,y)=some (delta,0); rw [sub_eq_zero.mp xd,yz]
      · right; right; right; apply coordinates_injective
        rw [torsion_sum]
        change some (x,y)=some (-delta,0)
        rw [eq_neg_of_add_eq_zero_left right,yz]
  · rintro (rfl|rfl|rfl|rfl)
    · simp
    · exact twiceT
    · exact twiceU
    · rw [nsmul_add,twiceT,twiceU,zero_add]

private theorem twiceMultiple (m : ℤ) : (2:ℕ) • (m • R)=m • P := by
  rw [P_is_double,two_nsmul,zsmul_add]

/-- A representative for each coset of the doubled map is enough to recover
the exact generator hypothesis used by the physical signed-chart argument. -/
theorem generated_of_range (h : DoubledRange) : Generated := by
  intro Q
  have mem : (2:ℕ) • Q ∈ (nsmulAddMonoidHom (α:=Point) 2).range := ⟨Q,rfl⟩
  rw [show (nsmulAddMonoidHom (α:=Point) 2).range=AddSubgroup.zmultiples P from h] at mem
  obtain ⟨m,hm⟩:=AddSubgroup.mem_zmultiples_iff.mp mem
  have killed : (2:ℕ) • (Q-m • R)=0 := by rw [nsmul_sub,twiceMultiple,hm,sub_self]
  have represent : ∃ a d : Bool, Q-m • R=(if a then T else 0)+(if d then U else 0) := by
    rcases (two_torsion _).mp killed with h0|hT|hU|hTU
    · exact ⟨false,false,by simpa using h0⟩
    · exact ⟨true,false,by simpa using hT⟩
    · exact ⟨false,true,by simpa using hU⟩
    · exact ⟨true,true,hTU⟩
  obtain ⟨a,d,e⟩:=represent
  refine ⟨m,a,d,?_⟩
  calc Q=m • R+(Q-m • R) := by abel
       _ = _ := by rw [e,add_assoc]

/-- The doubled-range statement is equivalent to the particular generator
decomposition needed by the candidate. -/
theorem generated_iff_range : Generated ↔ DoubledRange := by
  refine ⟨?_,generated_of_range⟩
  intro group
  unfold DoubledRange
  ext Q
  constructor
  · rintro ⟨S,rfl⟩
    obtain ⟨m,a,d,e⟩:=group S
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m,?_⟩
    change m • P=(2:ℕ) • S
    rw [e,nsmul_add,nsmul_add,twiceMultiple]
    cases a <;> cases d <;> simp [twiceT,twiceU]
  · intro mem
    obtain ⟨m,rfl⟩:=AddSubgroup.mem_zmultiples_iff.mp mem
    exact ⟨m • R,twiceMultiple m⟩

/-- Transport the certificate from another presentation of C. The marked half-point
must map to this circuit's R. -/
theorem range_transport {A : Type*} [AddCommGroup A] (e : A ≃+ Point) (S : A)
    (mark : e S=R) (source : (nsmulAddMonoidHom (α:=A) 2).range=
      AddSubgroup.zmultiples ((2:ℕ) • S)) : DoubledRange := by
  unfold DoubledRange
  ext Q
  constructor
  · rintro ⟨X,rfl⟩
    have mem : (2:ℕ) • e.symm X ∈ (nsmulAddMonoidHom (α:=A) 2).range := ⟨e.symm X,rfl⟩
    rw [source] at mem
    obtain ⟨m,hm⟩:=AddSubgroup.mem_zmultiples_iff.mp mem
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m,?_⟩
    change m • P=(2:ℕ) • X
    simpa only [map_zsmul,map_nsmul,mark,e.apply_symm_apply,P] using congrArg e hm
  · intro mem
    obtain ⟨m,rfl⟩:=AddSubgroup.mem_zmultiples_iff.mp mem
    exact ⟨m • R,twiceMultiple m⟩

/-- The dyadic reciprocal law alone makes the signed index injective. -/
theorem signed_index_injective : Function.Injective (fun n : ℤ=>n • P) := by
  have nz (n : ℤ) (hn : n≠0) : n • P≠0 := by
    intro eq
    have nr : (n:ℚ)≠0 := by exact_mod_cast hn
    have unit:=(Prime23.Actual.actual_normalized n hn).1
    apply unit.nonzero (by decide) (by decide +kernel) nr
    change coeffs (ReciprocalDivision.reciprocal (D:=D) (n • P))=(0,0)
    rw [eq,Prime23.Actual.reciprocal_fromCoordinates]
    rfl
  intro i j eq
  change i • P=j • P at eq
  by_contra different
  exact nz (i-j) (sub_ne_zero.mpr different) (by simp [sub_zsmul,eq])

theorem physical_labels_of_range (certificate : DoubledRange) (y : Fin 80→Rat)
    (zero : Binding.V y 9813=0) :
    ∃ n : Fin 4→ℤ, (∀i, n i≠0 ∧ chartPoint (physical_root_charts y zero i).1=n i • P) ∧
      (∀i, n i%2=1) ∧ n 1-1≠0 ∧ ((2:ℤ)*3^1474)∣n 1-1 :=
  Prime23.Physical.physical_anchor_labels (generated_of_range certificate) y zero

#print axioms two_torsion
#print axioms generated_iff_range
#print axioms range_transport
#print axioms signed_index_injective
#print axioms physical_labels_of_range
end Candidate80
