import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Detection of genuine relative morphisms from all geometric points. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.MarkedPicard
universe u v w
abbrev Point {K : Type u} [Field K] {X : Scheme.{u}} (s : X ⟶ Spec (.of K)) :=
  {p : Spec (.of K) ⟶ X // p ≫ s=𝟙 _}

theorem ext_points {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) (t : Y ⟶ Spec (.of K))
    [IsReduced X] [LocallyOfFiniteType s] [LocallyOfFiniteType t] [IsSeparated t]
    {a b : X ⟶ Y} (ha : a ≫ t=s) (hb : b ≫ t=s)
    (h : ∀ p : Point s, p.val ≫ a=p.val ≫ b) : a=b := by
  let : LocallyOfFiniteType (a ≫ t) := ha.symm ▸ inferInstanceAs (LocallyOfFiniteType s)
  apply AlgebraicGeometry.ext_of_apply_eq t Set.univ isOpen_univ.isLocallyClosed dense_univ _ (ha.trans hb.symm)
  intro x _ hx
  have hw := h ⟨pointOfClosedPoint s x hx,pointOfClosedPoint_comp s x hx⟩
  have v := congrArg (fun f : Spec (.of K) ⟶ Y => f (IsLocalRing.closedPoint K)) hw
  change a (pointOfClosedPoint s x hx (IsLocalRing.closedPoint K)) =
    b (pointOfClosedPoint s x hx (IsLocalRing.closedPoint K)) at v
  have hp : (pointOfClosedPoint s x hx) (IsLocalRing.closedPoint K) = x :=
    pointOfClosedPoint_apply s x hx _
  exact (congrArg a hp).symm.trans (v.trans (congrArg b hp))

/-- Geometric points are written as degree-zero classes. The sign of a
polarized endomorphism is not an input to this comparison. -/
structure Comparison {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) (inv : X ⟶ X) (P : Type v) (ι : P → P)
    (G : Type w) [AddCommGroup G] where
  abel : P → G
  generate : AddSubgroup.closure (Set.range (fun r : P × P => abel r.1-abel r.2))=⊤
  fibres : ∀ p q, abel p+abel (ι p)=abel q+abel (ι q)
  point : G ≃ Point s
  inversion : ∀ g, (point g).val ≫ inv=(point (-g)).val

def Comparison.represents {K : Type u} [Field K] {X : Scheme.{u}} {s : X ⟶ Spec (.of K)}
    {inv : X ⟶ X} {P : Type v} {ι : P → P} {G : Type w} [AddCommGroup G]
    (D : Comparison s inv P ι G) (a : X ⟶ X) (f : G →+ G) : Prop :=
  a ≫ s=s ∧ ∀ g, (D.point g).val ≫ a=(D.point (f g)).val

variable {K : Type u} [Field K] {X : Scheme.{u}} {s : X ⟶ Spec (.of K)}
  {inv : X ⟶ X} {P : Type v} {ι : P → P} {G : Type w} [AddCommGroup G]

theorem Comparison.faithful [IsAlgClosed K] [IsReduced X] [LocallyOfFiniteType s] [IsSeparated s]
    (D : Comparison s inv P ι G) {a b : X ⟶ X} {f : G →+ G}
    (ha : D.represents a f) (hb : D.represents b f) : a=b := by
  apply ext_points s s ha.1 hb.1
  intro p
  obtain ⟨g,rfl⟩ := D.point.surjective p
  exact (ha.2 g).trans (hb.2 g).symm

theorem Comparison.represents_id (D : Comparison s inv P ι G) :
    D.represents (𝟙 _) (AddMonoidHom.id G) :=
  ⟨Category.id_comp _,fun _ => Category.comp_id _⟩

theorem Comparison.represents_inv (D : Comparison s inv P ι G) (hi : inv ≫ s=s) :
    D.represents inv (-(AddMonoidHom.id G)) := ⟨hi,D.inversion⟩

end ZInQBlueprint.MarkedPicard
#print axioms ZInQBlueprint.MarkedPicard.ext_points
#print axioms ZInQBlueprint.MarkedPicard.Comparison.faithful
#print axioms ZInQBlueprint.MarkedPicard.Comparison.represents_id
#print axioms ZInQBlueprint.MarkedPicard.Comparison.represents_inv
