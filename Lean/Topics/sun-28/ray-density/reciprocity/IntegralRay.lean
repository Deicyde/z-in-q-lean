import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace Sun28.Reciprocity
open Ideal
noncomputable section
variable {R:Type*} [CommRing R] (M:Ideal R)

abbrev residue := Ideal.Quotient.mk M
abbrev principal (x:R) := Ideal.span {x}
abbrev unitReduction := Units.map (residue M).toMonoidHom
abbrev unitClasses := (R ⧸ M)ˣ ⧸ (unitReduction M).range
def classOf (x:R) (h:IsUnit (residue M x)) : unitClasses M :=
  QuotientGroup.mk' _ h.unit

/-- The integral-ideal clause of ray equivalence; Gaussian rings have no real sign conditions. -/
def idealEquivalent (A B:Ideal R) : Prop :=
  ∃ c d:R, c≠0 ∧ d≠0 ∧ residue M c=1 ∧ residue M d=1 ∧ principal c*A=principal d*B

theorem invertible_iff (x:R) : IsUnit (residue M x) ↔ principal x ⊔ M=⊤ := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨t,ht⟩:=Ideal.Quotient.mk_surjective ((v⁻¹ : (R ⧸ M)ˣ) : R ⧸ M)
    have e : residue M (t*x)=1 := by rw [map_mul,ht,←hv];simp
    have h : 1-t*x∈M := (Ideal.Quotient.eq (I:=M)).mp (by change residue M 1 = residue M (t*x);rw [map_one,e])
    exact (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_singleton_sup.mpr ⟨t,1-t*x,h,by ring⟩)
  · intro top
    obtain ⟨t,b,hb,e⟩:=Ideal.mem_span_singleton_sup.mp ((Ideal.eq_top_iff_one _).mp top)
    have rel:=congrArg (residue M) e
    rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr hb,add_zero,map_one] at rel
    exact isUnit_iff_exists_inv'.mpr ⟨residue M t,rel⟩

theorem class_eq (x y:R) (hx:IsUnit (residue M x)) (hy:IsUnit (residue M y)) :
    classOf M x hx=classOf M y hy ↔
      ∃ u:Rˣ,residue M x*residue M (u:R)=residue M y := by
  change QuotientGroup.mk' _ hx.unit=QuotientGroup.mk' _ hy.unit ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_,⟨u,rfl⟩,h⟩
    refine ⟨u,?_⟩
    simpa [unitReduction,IsUnit.unit_spec] using congrArg Units.val h
  · rintro ⟨u,e⟩
    exact ⟨_,⟨u,rfl⟩,Units.ext (by simpa [unitReduction,IsUnit.unit_spec] using e)⟩

/-- This equivalence produces both integral multipliers, not a formal ideal quotient. -/
theorem principal_ray_iff [IsDomain R] [Nontrivial (R ⧸ M)] (x y:R)
    (hx:IsUnit (residue M x)) (hy:IsUnit (residue M y)) :
    idealEquivalent M (principal x) (principal y) ↔ classOf M x hx=classOf M y hy := by
  rw [class_eq]
  constructor
  · rintro ⟨c,d,_,_,hc,hd,h⟩
    rw [Ideal.span_singleton_mul_span_singleton,Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_eq_span_singleton] at h
    obtain ⟨u,e⟩:=h
    refine ⟨u,?_⟩
    simpa [map_mul,hc,hd] using congrArg (residue M) e
  · rintro ⟨u,e⟩
    obtain ⟨t,ht⟩:=Ideal.Quotient.mk_surjective ((hy.unit⁻¹ : (R ⧸ M)ˣ) : R ⧸ M)
    have hyt : residue M (y*t)=1 := by rw [map_mul,ht];calc
      _ = (hy.unit : R ⧸ M) * ((hy.unit⁻¹ : (R ⧸ M)ˣ) : R ⧸ M) := congrArg (fun a : R ⧸ M => a * _) hy.unit_spec.symm
      _ = 1 := hy.unit.val_inv
    have hxt : residue M (x*(u:R)*t)=1 := by
      rw [map_mul,map_mul,e,←map_mul,hyt]
    have nz {a:R} (h:residue M a=1) : a≠0 := fun z=>by simp [z] at h
    refine ⟨y*t,x*(u:R)*t,nz hyt,nz hxt,hyt,hxt,?_⟩
    rw [Ideal.span_singleton_mul_span_singleton,Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_eq_span_singleton]
    exact ⟨u,by ring⟩

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.invertible_iff
#print axioms Sun28.Reciprocity.class_eq
#print axioms Sun28.Reciprocity.principal_ray_iff
