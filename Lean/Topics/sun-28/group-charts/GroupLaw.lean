import GuardProgram

namespace Sun28.GroupCharts
open ZInQ WeierstrassCurve WeierstrassCurve.Affine

namespace Quad
variable {R : Type*} [CommRing R] {φ : R →+* ℚ}

structure Value (φ : R →+* ℚ) (x : Quad R) (v : K0) : Prop where
  good : Good φ x
  value : eval φ x = v

namespace Value
variable {x y : Quad R} {a b : K0}
theorem neg (h : Value φ x a) : Value φ x.neg (-a) :=
  ⟨h.good,by rw [eval_neg,h.value]⟩
theorem add (h : Value φ x a) (k : Value φ y b) : Value φ (x.add y) (a+b) :=
  ⟨(good_add ..).2 ⟨h.good,k.good⟩,by rw [eval_add φ h.good k.good,h.value,k.value]⟩
theorem sub (h : Value φ x a) (k : Value φ y b) : Value φ (x.sub y) (a-b) :=
  ⟨(good_sub ..).2 ⟨h.good,k.good⟩,by rw [eval_sub φ h.good k.good,h.value,k.value]⟩
theorem mul (h : Value φ x a) (k : Value φ y b) : Value φ (x.mul y) (a*b) :=
  ⟨(good_mul ..).2 ⟨h.good,k.good⟩,by rw [eval_mul φ h.good k.good,h.value,k.value]⟩
theorem div (h : Value φ x a) (k : Value φ y b) (nz : b≠0) : Value φ (x.div y) (a/b) := by
  have e : eval φ y≠0 := k.value ▸ nz
  exact ⟨(good_div φ k.good).2 ⟨h.good,e⟩,by rw [eval_div φ h.good k.good e,h.value,k.value]⟩
theorem normNum (h : Value φ x a) : φ x.normNum=0 ↔ a=0 := by
  rw [normNum_zero_iff φ h.good,h.value]
end Value
end Quad

inductive PointCode (R : Type*) where
  | infinity
  | affine (x y : Quad R)

/-- The affine constructor always represents a nonsingular point of the paper's curve. -/
inductive Represents {R : Type*} [CommRing R] (φ : R →+* ℚ) :
    PointCode R → curveC.toAffine.Point → Prop
  | infinity : Represents φ .infinity 0
  | affine {x y X Y} (h : curveC.toAffine.Nonsingular X Y)
      (hx : Quad.Value φ x X) (hy : Quad.Value φ y Y) :
      Represents φ (.affine x y) (.some X Y h)

namespace PointCode
variable {R : Type*} [CommRing R]

def coefficient : Quad R := .ofPair (-11) 6

theorem coefficient_value (φ : R →+* ℚ) : Quad.Value φ (coefficient (R:=R)) (-delta^2) := by
  refine ⟨Quad.good_pair φ (-11) 6, ?_⟩
  rw [coefficient,Quad.eval_pair,delta_sq]
  ext <;> norm_num [map_ofNat]

def chord (x u y slope : Quad R) : PointCode R :=
  let x' := ((slope.mul slope).sub x).sub u
  .affine x' ((slope.mul (x.sub x')).sub y)

def tangentSlope (x y : Quad R) : Quad R :=
  let xx := x.mul x
  (((xx.add xx).add xx).add coefficient).div (y.add y)

def addProgram : PointCode R → PointCode R → Program R (PointCode R)
  | .infinity,q => .pure q
  | p,.infinity => .pure p
  | .affine x y,.affine u v =>
    .branch (x.sub u).normNum
      (.branch (y.add v).normNum (.pure .infinity) (.pure (chord x u y (tangentSlope x y))))
      (.pure (chord x u y ((y.sub v).div (x.sub u))))

private theorem chord_correct (φ : R →+* ℚ) {x u y slope : Quad R} {X U Y V : K0}
    {h : curveC.toAffine.Nonsingular X Y} {k : curveC.toAffine.Nonsingular U V}
    (hx : Quad.Value φ x X) (hu : Quad.Value φ u U) (hy : Quad.Value φ y Y)
    (nv : ¬(X=U ∧ Y=curveC.toAffine.negY U V))
    (hs : Quad.Value φ slope (curveC.toAffine.slope X U Y V)) :
    Represents φ (chord x u y slope) (.some X Y h+.some U V k) := by
  rw [Point.add_some nv]
  apply Represents.affine
  · convert ((hs.mul hs).sub hx).sub hu using 1
    simp only [Affine.addX,curveC,shortCurve_a₁,shortCurve_a₂]
    ring
  · convert (hs.mul (hx.sub (((hs.mul hs).sub hx).sub hu))).sub hy using 1
    simp only [Affine.addY,Affine.negAddY,Affine.addX,curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂]
    ring

theorem add_correct (φ : R →+* ℚ) {p q : PointCode R} {P Q : curveC.toAffine.Point}
    (hp : Represents φ p P) (hq : Represents φ q Q) :
    Represents φ (Program.eval φ (addProgram p q)) (P+Q) := by
  cases hp with
  | infinity => simpa [addProgram,Program.eval] using hq
  | @affine x y X Y h hx hy =>
    cases hq with
    | infinity => simpa [addProgram,Program.eval] using (Represents.affine h hx hy)
    | @affine u v U V k hu hv =>
      have dx := hx.sub hu
      have sy := hy.add hv
      by_cases e : X=U
      · have g : φ (x.sub u).normNum=0 := dx.normNum.mpr (sub_eq_zero.mpr e)
        by_cases t : Y = curveC.toAffine.negY U V
        · have yz : Y = -V := by simpa only [curveC,shortCurve_negY] using t
          have r : φ (y.add v).normNum=0 := sy.normNum.mpr (by rw [yz,neg_add_cancel])
          rw [Point.add_of_Y_eq e t]
          simpa [addProgram,Program.eval,g,r] using (Represents.infinity (φ:=φ))
        · have ey : Y=V := (Affine.Y_eq_of_X_eq h.1 k.1 e).resolve_right t
          have s : Y+V≠0 := by
            intro z
            apply t
            rw [curveC,shortCurve_negY]
            exact eq_neg_of_add_eq_zero_left z
          have r : φ (y.add v).normNum≠0 := (not_congr sy.normNum).2 s
          simp only [addProgram,Program.eval,ite_eq_left g,ite_eq_right r]
          apply chord_correct φ hx hu hy (fun terms => t terms.2)
          rw [Affine.slope_of_Y_ne e t]
          simp only [curveC,shortCurve_negY,shortCurve_a₁,shortCurve_a₂,shortCurve_a₄]
          have yy : Y+Y≠0 := by simpa only [←ey] using s
          have xx := hx.mul hx
          rw [sub_neg_eq_add]
          have num : 3*X^2+2*0*X+ -delta^2-0*Y=X*X+X*X+X*X+ -delta^2 := by ring
          rw [num]
          exact (((xx.add xx).add xx).add (coefficient_value φ)).div (hy.add hy) yy
      · have diff : X-U≠0 := sub_ne_zero.mpr e
        have g : φ (x.sub u).normNum≠0 := (not_congr dx.normNum).2 diff
        simp only [addProgram,Program.eval,ite_eq_right g]
        apply chord_correct φ hx hu hy (fun terms => e terms.1)
        rw [Affine.slope_of_X_ne e]
        exact (hy.sub hv).div dx diff

end PointCode
#print axioms PointCode.add_correct
end Sun28.GroupCharts
