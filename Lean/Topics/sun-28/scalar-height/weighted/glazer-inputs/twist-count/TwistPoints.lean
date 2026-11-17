import TwistAssignments

/-! A count of rational points on each literal sextic supplies the sign-and-prime certificate. -/
namespace ZInQBlueprint.TwistCount
open Finset Sun28.FiveDescent ZInQBlueprint.OriginalHeightCount
open scoped Classical
noncomputable section
set_option maxRecDepth 12000
attribute [local irreducible] D E Sun28.Ordinary.glazerConstant24

def position (d e : ℤ) (p : ℕ) : Fin 3 :=
  if p∈d.natAbs.primeFactors then if p∈e.natAbs.primeFactors then 2 else 0 else 1

def primeCost (d e : ℤ) : ℕ := ∏ p ∈ parameterPrimes d e,choiceWeight (position d e p)

theorem cost_eq {x : ℚ} {m : ℕ} (hx : label x=m) :
    primeCost (D x.num x.den) (E x.num x.den)=assignmentWeight (code m x) := by
  subst m
  have eq : parameterPrimes (D x.num x.den) (E x.num x.den)=(label x).primeFactors :=
    (label_factors x).symm
  rw [primeCost,eq,←prod_attach]
  rfl

private theorem squarefree_determined {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b)
    (f : a.natAbs.primeFactors=b.natAbs.primeFactors) (s : (a<0 ↔ b<0)) : a=b := by
  have nat : a.natAbs=b.natAbs := by
    calc
      _ = ∏ p ∈ a.natAbs.primeFactors,p := (Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr sa)).symm
      _ = _ := by rw [f]
      _ = b.natAbs := Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr sb)
  omega

theorem same_twist {x y : ℚ} {m : ℕ} (ox : offMarks x) (oy : offMarks y)
    (lx : label x=m) (ly : label y=m) (sg : signs x=signs y) (types : code m x=code m y) :
    D x.num x.den=D y.num y.den ∧ E x.num x.den=E y.num y.den := by
  let d (z:ℚ) := D z.num z.den
  let e (z:ℚ) := E z.num z.den
  have partition (z : ℚ) (lab : label z=m) :
      (d z).natAbs.primeFactors ∪ (e z).natAbs.primeFactors=m.primeFactors := by
    rw [←lab];exact (label_factors z).symm
  have px:=partition x lx
  have py:=partition y ly
  have classes (p : ℕ) :
      (p∈(d x).natAbs.primeFactors ↔ p∈(d y).natAbs.primeFactors) ∧
      (p∈(e x).natAbs.primeFactors ↔ p∈(e y).natAbs.primeFactors) := by
    by_cases inM : p∈m.primeFactors
    · have cmp:=congrFun types ⟨p,inM⟩
      change position (d x) (e x) p=position (d y) (e y) p at cmp
      have liveX : p∈(d x).natAbs.primeFactors ∨ p∈(e x).natAbs.primeFactors := mem_union.mp (by simpa only [px] using inM)
      have liveY : p∈(d y).natAbs.primeFactors ∨ p∈(e y).natAbs.primeFactors := mem_union.mp (by simpa only [py] using inM)
      unfold position at cmp
      by_cases xd : p∈(d x).natAbs.primeFactors <;> by_cases xe : p∈(e x).natAbs.primeFactors <;>
        by_cases yd : p∈(d y).natAbs.primeFactors <;> by_cases ye : p∈(e y).natAbs.primeFactors <;>
        simp only [xd,xe,yd,ye,ite_true,ite_false] at cmp liveX liveY ⊢ <;> tauto
    · have xx : p∉(d x).natAbs.primeFactors ∪ (e x).natAbs.primeFactors := by simpa only [px] using inM
      have yy : p∉(d y).natAbs.primeFactors ∪ (e y).natAbs.primeFactors := by simpa only [py] using inM
      simp only [mem_union,not_or] at xx yy
      simp [xx.1,xx.2,yy.1,yy.2]
  have dset := Finset.ext (fun p=>(classes p).1)
  have eset := Finset.ext (fun p=>(classes p).2)
  have sgD : (d x<0) ↔ d y<0 := by
    have z:=congrArg Prod.fst sg
    simpa [signs,d] using z
  have sgE : (e x<0) ↔ e y<0 := by
    have z:=congrArg Prod.snd sg
    simpa [signs,e] using z
  obtain ⟨dx,ex,_⟩:=forward ox
  obtain ⟨dy,ey,_⟩:=forward oy
  exact ⟨squarefree_determined dx dy dset sgD,squarefree_determined ex ey eset sgE⟩

/-- The only geometric input is a finite-set count on the displayed affine twists. -/
def PointCount (C : ℝ) : Prop :=
  ∀ d e : ℤ, Squarefree d → Squarefree e → ∀ Y : Finset (ℚ×ℚ),
    (∀ q∈Y, q.1≠0 ∧ q.2≠0 ∧ (e:ℚ)*q.2^2=sextic d q.1) →
    (Y.card:ℝ)≤C*primeCost d e

theorem certificate_of_pointCount {C : ℝ} (c : 0≤C) (point : PointCount C) : TwistCountCertificate C := by
  intro m s f X properties
  rcases X.eq_empty_or_nonempty with empty|live
  · simp [empty]; positivity
  obtain ⟨base,basein⟩:=live
  obtain ⟨offB,labB,signB,codeB⟩:=properties base basein
  let d:=D base.num base.den
  let e:=E base.num base.den
  obtain ⟨sd,se,_⟩:=forward offB
  have lifts (x : ↥X) : ∃ q : ℚ×ℚ, q.1≠0 ∧ q.2≠0 ∧ (e:ℚ)*q.2^2=sextic d q.1 ∧ parameter d q.1=(x:ℚ) := by
    obtain ⟨off,lab,sg,cd⟩:=properties x x.2
    obtain ⟨dx,ex⟩:=same_twist off offB lab labB (sg.trans signB.symm) (cd.trans codeB.symm)
    obtain ⟨_,_,u,v,un,vn,eq,back⟩:=forward off
    rw [dx,ex] at eq
    rw [dx] at back
    exact ⟨(u,v),un,vn,eq,back.trans (x:ℚ).num_div_den⟩
  choose g hg using lifts
  have inj : Function.Injective g := by
    intro x y eq
    apply Subtype.ext
    exact (hg x).2.2.2.symm.trans ((congrArg (fun q:ℚ×ℚ=>parameter d q.1) eq).trans (hg y).2.2.2)
  let Y:=univ.image g
  have card : Y.card=X.card := by
    change (univ.image g).card=X.card
    rw [card_image_of_injective _ inj,card_univ,Fintype.card_coe]
  have sol (q : ℚ×ℚ) (hq:q∈Y) : q.1≠0 ∧ q.2≠0 ∧ (e:ℚ)*q.2^2=sextic d q.1 := by
    obtain ⟨x,_,rfl⟩:=mem_image.mp hq
    exact ⟨(hg x).1,(hg x).2.1,(hg x).2.2.1⟩
  have result:=point d e sd se Y sol
  rw [card] at result
  simpa only [d,e,cost_eq labB,codeB] using result

theorem exceptional_count {B K : ℕ} {C : ℝ} (c : 0≤C) (point : PointCount C)
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    ((exceptions B).card:ℝ)≤4*C*(K:ℝ)*(1+Real.log (K:ℝ))^2498 :=
  exceptional_count_of_twists c (certificate_of_pointCount c point) threshold

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.cost_eq
#print axioms ZInQBlueprint.TwistCount.same_twist
#print axioms ZInQBlueprint.TwistCount.certificate_of_pointCount
#print axioms ZInQBlueprint.TwistCount.exceptional_count
