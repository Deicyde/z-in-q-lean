import AnchorResidues
import OddActualResidue
import LocalConsequence
import AnchorCollision
import SignedLabels
import TranslatedReciprocal

namespace Prime23.Physical
open PhysicalProjection.Comparison (Q2 times sq norm)
open PhysicalProjection.RootOrdinate (root)
open EllipticOrbit.Field
open EllipticHeight.Labels
open StructuralReduction StructuralReduction.Transfer84
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.Comparison
open WeierstrassCurve.Affine
open Prime23.Actual (orbit)

private def a : K := ofPair (-1,7/4)
private def b : K := ofPair (39/8,-9/2)
private theorem marked_curve : b^2=a^4-D := by decide +kernel
private theorem markedNS : E.toAffine.Nonsingular (a^2) (a*b) :=
  (equation_iff_nonsingular (W:=E)).mp ((equation ..).mpr (by decide +kernel))
private theorem marked_point : P=(WeierstrassCurve.Affine.Point.some markedNS : Point) := by
  apply coordinates_injective
  rw [P_pair]
  decide +kernel

/-- The complete quadratic number whose second coefficient is the scalar row operand. -/
def differenceRoot (h j : Q2) : Q2 :=
  times (AnchorCircuit.numerator h j) (inverse (AnchorCircuit.divisor h))

theorem difference_coefficient (h j : Q2) :
    (differenceRoot h j).2=AnchorCircuit.shifted h j := by
  unfold differenceRoot AnchorCircuit.shifted
  dsimp [times,inverse,PhysicalProjection.RootOrdinate.conjugate]
  ring

private theorem denominator (h : Q2) : ofPair (AnchorCircuit.divisor h)=a^2*(ofPair h)^2+D := by
  have e : AnchorCircuit.divisor h=plus (PhysicalProjection.Comparison.sq (times (-1,7/4) h)) Base.D := by
    apply Prod.ext <;> simp [AnchorCircuit.divisor,plus,Base.D,sub_eq_add_neg]
  rw [e]
  change ofPair (PhysicalProjection.Comparison.sq (times (-1,7/4) h))+D=a^2*(ofPair h)^2+D
  rw [ofPair_sq,ofPair_mul]
  unfold a; ring

private theorem mixed (h j : Q2) :
    ofPair (differenceRoot h j)*(a^2*(ofPair h)^2+D)=a*ofPair j-b*ofPair h := by
  let d:=AnchorCircuit.divisor h
  let t:=AnchorCircuit.numerator h j
  have dn : norm d≠0 := ne_of_gt (AnchorCircuit.norm_positive h)
  have cancel : ofPair d*ofPair (inverse d)=1 := by rw [←ofPair_mul,inverse_clears dn]; rfl
  have val : ofPair t=a*ofPair j-b*ofPair h := by
    change ofPair (PhysicalProjection.RootOrdinate.sub _ _)=_
    rw [ofPair_sub,ofPair_mul,ofPair_mul]; rfl
  rw [←denominator]
  change ofPair (times t (inverse d))*ofPair d=_
  rw [ofPair_mul]
  calc _ = ofPair t*(ofPair d*ofPair (inverse d)) := by ring
       _ = _ := by rw [cancel,mul_one,val]

private theorem inv_of_product {x g : K} (h : x*g=1) : x⁻¹=g := by
  have nz : x≠0 := by intro z; rw [z,zero_mul] at h; exact zero_ne_one h
  calc x⁻¹=x⁻¹*1 := (mul_one _).symm
       _ = _ := by rw [←h,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

/-- The rational-function identity at the translated point, including the tangent at −P. -/
theorem translated_reciprocal {h j : Q2} (rt : root h j) (ne : chartPoint rt≠P) :
    ActualBase.fromCoordinates (chartPoint rt-P)=(ofPair (differenceRoot h j))^2 := by
  let H:=ofPair h
  let J:=ofPair j
  let G:=ofPair (differenceRoot h j)
  have rt' : J^2=H^4-D := (root_iff ..).mp rt
  have mx : G*(a^2*H^2+D)=a*J-b*H := mixed h j
  have nsg : E.toAffine.Nonsingular (H^2) (H*J) := quartic_nonsingular rt
  have qEq : chartPoint rt=(WeierstrassCurve.Affine.Point.some nsg : Point) := rfl
  by_cases same : H^2=a^2
  · rcases Y_eq_of_X_eq nsg.1 markedNS.1 same with yy|yy
    · have coll : chartPoint rt=P := by
        apply coordinates_injective
        rw [qEq,marked_point]
        change some (H^2,H*J)=some (a^2,a*b)
        rw [same,yy]
      exact (ne coll).elim
    · rw [negY] at yy
      have opposite : chartPoint rt= -P := by
        apply coordinates_injective
        rw [qEq,marked_point,WeierstrassCurve.Affine.Point.neg_some]
        change some (H^2,H*J)=some (a^2,E.toAffine.negY (a^2) (a*b))
        rw [negY,same,yy]
      have val : ofPair Base.xDouble*G^2=1 :=
        AnchorCollision.Translation.tangent marked_curve rt' same yy mx
          (by decide +kernel) (by decide +kernel)
      have two : (-P)-P= -((2:ℕ) • P) := by rw [two_nsmul]; abel
      have neg (S : Point) : ActualBase.fromCoordinates (-S)=ActualBase.fromCoordinates S := by
        cases S <;> rfl
      rw [opposite,two,neg]
      change ActualBase.fromCoordinates ((2:ℕ) • P)=G^2
      unfold ActualBase.fromCoordinates
      rw [ActualBase.double_pair]
      exact inv_of_product val
  · let L:=E.toAffine.slope (H^2) (a^2) (H*J) (E.toAffine.negY (a^2) (a*b))
    let X:=E.toAffine.addX (H^2) (a^2) L
    have xx : ActualBase.fromCoordinates (chartPoint rt-P)=X⁻¹ := by
      rw [qEq,marked_point,sub_eq_add_neg,WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.add_of_X_ne same]
      rfl
    have line : L*(H^2-a^2)=H*J+a*b := by
      dsimp only [L]
      rw [slope_of_X_ne same,negY,div_mul_cancel₀ _ (sub_ne_zero.mpr same)]
      ring
    have xeq : X=L^2-H^2-a^2 := by
      dsimp only [X,WeierstrassCurve.Affine.addX,E]; ring
    have dn : a^2*H^2+D≠0 := by
      rw [←mul_pow]; exact square_plus_D_ne_zero (a*H)
    exact xx.trans (inv_of_product (AnchorCollision.Translation.chord marked_curve rt' dn mx
       (sub_ne_zero.mpr same) line xeq))

private theorem square_reciprocal {h j : Q2} (rt : root h j) {n : ℤ} (atPoint : chartPoint rt=n • P) :
    times (PhysicalProjection.Comparison.sq h) (orbit P n)=(1,0) := by
  have nn : ofPair h≠0 := fun z=>PhysicalProjection.RootOrdinate.root_nonzero rt (congrArg coeffs z)
  apply ofPair_injective
  rw [ofPair_mul,ofPair_sq]
  change (ofPair h)^2*ReciprocalDivision.reciprocal (D:=D) (n • P)=1
  rw [←atPoint,Actual.reciprocal_fromCoordinates]
  change (ofPair h)^2*((ofPair h)^2)⁻¹=1
  exact mul_inv_cancel₀ (pow_ne_zero 2 nn)

private theorem odd_chart {h j : Q2} (rt : root h j) {n : ℤ} (atPoint : chartPoint rt=n • P)
    (odd : n%2=1) : PairRed 3 (PhysicalProjection.Comparison.sq h) (0,1) := by
  obtain ⟨x,y,xy,red⟩:=OddActual.odd_abscissa n odd
  rw [←atPoint] at xy
  change some ((ofPair h)^2,ofPair h*ofPair j)=some (x,y) at xy
  have e:=(ofPair_sq h).trans (congrArg Prod.fst (Option.some.inj xy))
  have eq : PhysicalProjection.Comparison.sq h=coeffs x := congrArg coeffs e
  rw [eq]; exact red

private theorem second_ne {y : Fin 80→Rat} (zero : Binding.V y 9813=0) :
    chartPoint (physical_root_charts y zero 1).1≠P := by
  let h:=rootH (decoded y) 1
  let j:=rootJ (decoded y) 1
  intro e
  have coords:=(congrArg coordinates e).trans P_pair
  change some ((ofPair h)^2,ofPair h*ofPair j)=some (ofPair Base.xP,ofPair Base.yP) at coords
  have x:=ofPair_injective ((ofPair_sq h).trans (congrArg Prod.fst (Option.some.inj coords)))
  have y':=ofPair_injective ((ofPair_mul h j).trans (congrArg Prod.snd (Option.some.inj coords)))
  have markX : Base.xP=PhysicalProjection.Comparison.sq ((-1,7/4):Q2) := by decide +kernel
  have markY : Base.yP=times ((-1,7/4):Q2) (39/8,-9/2) := by decide +kernel
  exact AnchorCollision.excludes_P80 y zero ⟨x.trans markX,y'.trans markY⟩

private theorem odd_of_order_zero {n : ℤ} (hn : n≠0) (h : intOrder 2 n=0) : n%2=1 := by
  obtain ⟨u,ue,nu⟩:=int_split (p:=2) (by decide) n hn
  rw [h,Int.pow_zero,Int.one_mul] at ue
  have none : ¬(2:ℤ)∣n := ue ▸ nu
  omega

private theorem anchor_of_half (exponent : ℕ) {s m : ℤ} (half : s=2*m)
    (bound : exponent ≤ intOrder 3 m) : ((2:ℤ)*3^exponent)∣s := by
  have hp : BinaryQuartic.Prime 3 := prime_of_finite (by decide) (by decide)
  have ord : (exponent:ℤ) ≤ order 3 (m:Rat) := by
    rw [order_int hp]; exact Int.ofNat_le.mpr bound
  obtain ⟨t,ht⟩:=power_dvd_of_order hp ord
  refine ⟨t,?_⟩
  rw [half,ht,Int.natCast_pow,mul_assoc]
  rfl

private theorem offset_nonzero {Q : Point} {n : ℤ} (ne : Q≠P) (atPoint : Q=n • P) :
    n-1≠0 := sub_ne_zero.mpr (fun e=>ne (atPoint.trans (by rw [e,one_zsmul])))

private theorem shift_at_label {h j : Q2} {n : ℤ} (rt : root h j) (ne : chartPoint rt≠P)
    (atPoint : chartPoint rt=n • P) :
    PhysicalProjection.Comparison.sq (differenceRoot h j)=orbit P (n-1) := by
  apply ofPair_injective
  rw [ofPair_sq]
  change _=ReciprocalDivision.reciprocal (D:=D) ((n-1) • P)
  rw [sub_zsmul,one_zsmul,←atPoint,Actual.reciprocal_fromCoordinates]
  exact (translated_reciprocal rt ne).symm

private theorem label_order {h j : Q2} {n : ℤ} (rt : root h j) (hn : n≠0)
    (pt : chartPoint rt=n • P) :
    order 2 (norm (PhysicalProjection.Comparison.sq h))= -6-4*(intOrder 2 n:Int) := by
  have v:=dyadic_abscissa hn (Actual.actual_normalized n hn).1 (square_reciprocal rt pt)
  rwa [order_int (prime_of_finite (by decide) (by decide) : BinaryQuartic.Prime 2)] at v

private theorem label_shift_two {h j : Q2} {n : ℤ} (rt : root h j)
    (ne : chartPoint rt≠P) (pt : chartPoint rt=n • P) :
    ¬2∣(AnchorCircuit.shifted h j).den := by
  have ns:=offset_nonzero ne pt
  have v:=(dyadic_root ns (Actual.actual_normalized (n-1) ns).1 (shift_at_label rt ne pt)).2
  exact difference_coefficient h j ▸ v

private theorem half_off (n : ℤ) (odd : n%2=1) : n-1=2*((n-1)/2) := by omega

private theorem label_shift_three {h j : Q2} {n : ℤ} (rt : root h j)
    (ne : chartPoint rt≠P) (pt : chartPoint rt=n • P) (odd : n%2=1) :
    AnchorCircuit.shifted h j≠0 ∧
    order 3 (AnchorCircuit.shifted h j)= (intOrder 3 ((n-1)/2):Int)+1 := by
  let m:=(n-1)/2
  have off := offset_nonzero ne pt
  have f : n-1=2*m := half_off n odd
  have mn : m≠0 := fun z=>off (f.trans (by rw [z,mul_zero]))
  have root2 := (shift_at_label rt ne pt).trans (congrArg (orbit P) f)
  obtain ⟨_,nz,_,ord⟩:=triadic_root mn (Actual.actual_normalized m mn).2 root2
  rw [difference_coefficient] at nz ord
  rw [order_int (prime_of_finite (by decide) (by decide) : BinaryQuartic.Prime 3)] at ord
  exact ⟨nz,ord.trans (Int.add_comm _ _)⟩

private theorem product_three {y : Fin 80→Rat} (zero : Binding.V y 9813=0) {n : Fin 4→ℤ}
    (points : ∀ i, n i≠0 ∧ chartPoint (physical_root_charts y zero i).1=n i • P)
    (od : ∀ i, n i%2=1) : ¬3∣(AnchorCircuit.productReal (decoded y)).den := by
  have r (i : Fin 4):=odd_chart (physical_root_charts y zero i).1 (points i).2 (od i)
  exact (odd_product (r 0) (r 1) (r 2) (r 3)).2

/-- A zero of the physical polynomial forces the index constraints for every
labelling by actual signed points. No valuation, reduction or chart guard is assumed. -/
theorem index_conditions {y : Fin 80→Rat} (zero : Binding.V y 9813=0) {n : Fin 4→ℤ}
    (points : ∀ i, n i≠0 ∧ chartPoint (physical_root_charts y zero i).1=n i • P) :
    (∀ i, n i%2=1) ∧ n 1-1≠0 ∧ ((2:ℤ)*3^1474)∣n 1-1 := by
  let d (i : Fin 4):=intOrder 2 (n i)
  let k:=intOrder 3 ((n 1-1)/2)
  have odd (o : ∀i,d i=0) (i : Fin 4) : n i%2=1 := odd_of_order_zero (points i).1 (o i)
  have rt:=(physical_root_charts y zero 1).1
  have ne:=second_ne zero
  have pt:=(points 1).2
  have bounds:=AnchorCircuit.physical_index_orders zero d k
    (fun i=>label_order (physical_root_charts y zero i).1 (points i).1 (points i).2)
    (label_shift_two rt ne pt)
    (fun o=>⟨product_three zero points (odd o),label_shift_three rt ne pt (odd o 1)⟩)
  exact ⟨odd bounds.1,offset_nonzero ne pt,
    anchor_of_half 1474 (half_off _ (odd bounds.1 1)) bounds.2⟩

/-- Only the existing assertion on the Mordell–Weil generators is needed to
produce all four odd labels and the exceptional congruence at the second mark. -/
theorem physical_anchor_labels (group : EllipticOrbit.SignedLabels.Generated)
    (y : Fin 80→Rat) (zero : Binding.V y 9813=0) :
    ∃ n : Fin 4→ℤ, (∀i, n i≠0 ∧ chartPoint (physical_root_charts y zero i).1=n i • P) ∧
      (∀i, n i%2=1) ∧ n 1-1≠0 ∧ ((2:ℤ)*3^1474)∣n 1-1 := by
  obtain ⟨n,rep⟩:=EllipticOrbit.SignedLabels.physical_labels group y zero
  exact ⟨n,rep,index_conditions zero rep⟩

#print axioms translated_reciprocal
#print axioms index_conditions
#print axioms physical_anchor_labels
end Prime23.Physical
