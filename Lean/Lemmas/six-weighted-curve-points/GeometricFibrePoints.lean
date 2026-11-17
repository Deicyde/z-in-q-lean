import GluedCurvePoints
import Mathlib.FieldTheory.IsAlgClosed.Basic
/-! All geometric fibres of the given map of schemes, including the fibre
at the zero of the reciprocal coordinate. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] (f g : K[X]) (h : SexticOverlap K f g) (i : Bool) (x : K)
abbrev LineFibre := {m : Sections K (gluedOver K f g h) //
  m.left ≫ toLine K f g h = point K (RingHom.id K) x i}

def fibreOfOrdinate (y : { y : K // y^2 = aeval x (if i then g else f) }) : LineFibre f g h i x :=
  ⟨chartSection f g h i ⟨(x,y.1),y.2⟩,chartSection_line _ _ _ _ _⟩

def fibreEquiv : {y : K // y^2 = aeval x (if i then g else f)} ≃ LineFibre f g h i x := by
  apply Equiv.ofBijective (fibreOfOrdinate f g h i x)
  constructor
  · intro y w he
    have eq := chartSection_injective f g h i (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun p => p.1.2) eq)
  · rintro ⟨m,hm⟩
    obtain ⟨⟨⟨a,b⟩,hp⟩,ea,ep⟩ := chartSection_above f g h m i x hm.symm
    change a = x at ea
    subst a
    exact ⟨⟨b,hp⟩,Subtype.ext ep⟩

def nonzeroSquares [CharZero K] (w : K) (hw : w≠0) : Bool ≃ {y : K // y^2 = w^2} := by
  let q : Bool → {y : K // y^2=w^2} := fun b => ⟨if b then w else -w, by cases b <;> simp⟩
  apply Equiv.ofBijective q
  have wne : -w ≠ w := fun eq => hw (by linear_combination -(1/2:K)*eq)
  constructor
  · intro a b e
    have h₀ := congrArg Subtype.val e
    cases a <;> cases b
    · rfl
    · exact (wne h₀).elim
    · exact (wne h₀.symm).elim
    · rfl
  · rintro ⟨y,hy⟩
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hy) with yr | yr
    · exact ⟨true,Subtype.ext yr.symm⟩
    · exact ⟨false,Subtype.ext yr.symm⟩

theorem fibre_count [CharZero K] [IsAlgClosed K] [DecidableEq K] :
    Nat.card (LineFibre f g h i x) = if aeval x (if i then g else f) = 0 then 1 else 2 := by
  classical
  let a := aeval x (if i then g else f)
  rw [←Nat.card_congr (fibreEquiv f g h i x)]
  change Nat.card {y : K // y^2=a} = if a=0 then 1 else 2
  by_cases h0 : a=0
  · rw [h0,ite_eq_left rfl]
    let e : Unit ≃ {y : K // y^2=(0:K)} := {
      toFun := fun _ => ⟨0,by simp⟩, invFun := fun _ => ()
      left_inv := fun _ => rfl, right_inv := fun y => Subtype.ext (by by_contra he; exact (pow_ne_zero 2 (Ne.symm he)) y.2) }
    rw [←Nat.card_congr e]; simp
  · rw [ite_eq_right h0]
    obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < 2)
    have wn : w≠0 := fun e => h0 (by simp [←hw,e])
    rw [←hw,←Nat.card_congr (nonzeroSquares w wn)]
    simp
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.fibreEquiv
#print axioms ZInQBlueprint.WeightedCurvePoints.fibre_count
