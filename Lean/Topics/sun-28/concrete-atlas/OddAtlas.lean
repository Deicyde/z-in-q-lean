import AffineOrdinateAtlas
import PoleAtlas
import GroupLift
import RationalOdd

/-! The three dependent signed square roots in a single odd-index test. -/
namespace Sun28.Concrete
open Sun28.Ordinates Sun28.GroupCharts Sun28.WitnessIndices ZInQ
noncomputable section
variable {R : Type*} [CommRing R] {n : ℕ}
abbrev QuadAt (R : Type*) [CommRing R] (n : ℕ) := Quad (Test R n)

def up (q : QuadAt R n) : QuadAt R (n+1) := q.map (liftRoot n)
def squareRow (r : Concrete.Row R n) (k : Branch) (q : QuadAt R n) := r.signed k q.re q.im q.den
def squareOut (k : Branch) (q : QuadAt R n) : QuadAt R (n+1) :=
  let t := signedOutput k q.im q.den
  ⟨t.1,t.2.1,t.2.2⟩

theorem quad_square (r : Concrete.Row R n) (φ : R →+* ℚ) (t : Fin n → ℚ)
    (q : QuadAt R n) {a : K0} (hq : Quad.Value (ev φ t) q a) (y : K0) :
    (r.Holds φ t ∧ y^2=a) ↔ ∃ k w, (squareRow r k q).Holds φ (Fin.cons w t) ∧
        Quad.Value (ev φ (Fin.cons w t)) (squareOut k q) y := by
  have h := signed_square r φ t q.re q.im q.den y
  rw [← hq.value]
  refine Iff.trans ?_ (h.trans ?_)
  · change _ ↔ r.Holds φ t ∧ _ ∧ y^2=Quad.eval (ev φ t) q
    exact ⟨fun a => ⟨a.1,hq.good,a.2⟩,fun a => ⟨a.1,a.2.2⟩⟩
  · apply exists_congr
    intro k
    apply exists_congr
    intro w
    apply and_congr_right
    intro _
    exact ⟨fun h => ⟨h.1,h.2.symm⟩,fun h => ⟨h.good,h.value.symm⟩⟩

def epsCode : QuadAt R n := .ofPair 1 1
def twoCode : QuadAt R n := .ofPair 2 0

private theorem eps_spec (f : Test R n →+* ℚ) : Quad.Value f epsCode epsilon := by
  exact ⟨Quad.good_pair f 1 1,by simp [epsCode,epsilon]⟩

private theorem two_spec (f : Test R n →+* ℚ) : Quad.Value f twoCode (2:K0) := by
  refine ⟨Quad.good_pair f 2 0,?_⟩
  ext <;> norm_num [twoCode,Quad.eval,Quad.ofPair]

def middleArg (x y h : QuadAt R n) := twoCode.mul (x.add (y.div h))
def lastArg (x y h u : QuadAt R n) := (((u.mul h).add x).add (y.div h)).div epsCode

def oddRows (r : Concrete.Row R n) (x y : QuadAt R n) (b c d : Branch) : Concrete.Row R (n+3) :=
  let r₁ := squareRow r b x
  let h := squareOut b x
  let g := r₁.tested [] [h.normNum]
  let q := middleArg (up x) (up y) h
  let r₂ := squareRow g c q
  let u := squareOut c q
  squareRow r₂ d (lastArg (up (up x)) (up (up y)) (up h) u)

def oddRelation (x y : K0) : Prop :=
  ∃ h u v : K0, h≠0 ∧ h^2=x ∧ u^2=2*(x+y/h) ∧ v^2=(u*h+x+y/h)/epsilon

private theorem nonzero_norm (r : Concrete.Row R n) (φ : R →+* ℚ) (t : Fin n → ℚ)
    {q : QuadAt R n} {h : K0} (hq : Quad.Value (ev φ t) q h) :
    (r.tested [] [q.normNum]).Holds φ t ↔ r.Holds φ t ∧ h≠0 := by
  rw [tested_iff]
  simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,List.mem_singleton,forall_eq,true_and]
  exact and_congr_right (fun _ => not_congr hq.normNum)

private theorem prior_of_square (r : Concrete.Row R n) (φ : R →+* ℚ) (t : Fin n → ℚ)
    (q : QuadAt R n) (k : Branch) (w : ℚ) (h : (squareRow r k q).Holds φ (Fin.cons w t)) :
    r.Holds φ t := ((signed_iff ..).1 h).1

private theorem signed_value (r : Concrete.Row R n) (φ : R →+* ℚ) (t : Fin n → ℚ)
    (q : QuadAt R n) {a : K0} (hq : Quad.Value (ev φ t) q a) (k : Branch) (w : ℚ)
    (hs : (squareRow r k q).Holds φ (Fin.cons w t)) :
    ∃ y : K0, Quad.Value (ev φ (Fin.cons w t)) (squareOut k q) y ∧ y^2=a := by
  obtain ⟨_,hg,_⟩ := (signed_iff ..).1 hs
  let y := RootCharts.reconstruct k (ev φ t q.im) (ev φ t q.den) w
  have hy := (reads_output φ t k q.re q.im q.den w hg y).2 rfl
  have v : Quad.Value (ev φ (Fin.cons w t)) (squareOut k q) y := ⟨hy.1,hy.2.symm⟩
  exact ⟨y,v,((quad_square r φ t q hq y).2 ⟨k,w,hs,v⟩).2⟩

private theorem middle_spec {f : Test R n →+* ℚ} {x y h : QuadAt R n} {X Y H : K0}
    (hx : Quad.Value f x X) (hy : Quad.Value f y Y) (hh : Quad.Value f h H) (hn : H≠0) :
    Quad.Value f (middleArg x y h) (2*(X+Y/H)) :=
  (two_spec f).mul (hx.add (hy.div hh hn))

private theorem last_spec {f : Test R n →+* ℚ} {x y h u : QuadAt R n} {X Y H U : K0}
    (hx : Quad.Value f x X) (hy : Quad.Value f y Y) (hh : Quad.Value f h H)
    (hu : Quad.Value f u U) (hn : H≠0) :
    Quad.Value f (lastArg x y h u) ((U*H+X+Y/H)/epsilon) :=
  (((hu.mul hh).add hx).add (hy.div hh hn)).div (eps_spec f) epsilon_ne_zero

theorem odd_rows_spec (r : Concrete.Row R n) (φ : R →+* ℚ) (t : Fin n → ℚ)
    (x y : QuadAt R n) {X Y : K0} (hx : Quad.Value (ev φ t) x X) (hy : Quad.Value (ev φ t) y Y) :
    (r.Holds φ t ∧ oddRelation X Y) ↔
      ∃ (b c d : Branch) (s w z : ℚ), (oddRows r x y b c d).Holds φ (Fin.cons z (Fin.cons w (Fin.cons s t))) := by
  constructor
  · rintro ⟨hr,h,u,v,hn,he,ue,ve⟩
    obtain ⟨b,s,hs,hv⟩ := (quad_square r φ t x hx h).1 ⟨hr,he⟩
    have g := (nonzero_norm _ _ _ hv).2 ⟨hs,hn⟩
    have x₁ := lift_quad φ t s hx
    have y₁ := lift_quad φ t s hy
    have mid := middle_spec x₁ y₁ hv hn
    obtain ⟨c,w,hw,uv⟩ := (quad_square _ _ _ _ mid u).1 ⟨g,ue⟩
    have fin := last_spec (lift_quad φ _ w x₁) (lift_quad φ _ w y₁) (lift_quad φ _ w hv) uv hn
    obtain ⟨d,z,hz,_⟩ := (quad_square _ _ _ _ fin v).1 ⟨hw,ve⟩
    exact ⟨b,c,d,s,w,z,hz⟩
  · rintro ⟨b,c,d,s,w,z,H⟩
    dsimp only [oddRows] at H
    have hw := prior_of_square _ _ _ _ _ _ H
    have hg := prior_of_square _ _ _ _ _ _ hw
    obtain ⟨hs,_,ng⟩ := (tested_iff ..).1 hg
    obtain ⟨h,hv,he⟩ := signed_value _ _ _ _ hx _ _ hs
    have hn : h ≠ 0 := fun ez => ng _ (List.mem_singleton_self _) (hv.normNum.mpr ez)
    have x₁ := lift_quad φ t s hx
    have y₁ := lift_quad φ t s hy
    have mid := middle_spec x₁ y₁ hv hn
    obtain ⟨u,uv,ue⟩ := signed_value _ _ _ _ mid _ _ hw
    have fin := last_spec (lift_quad φ _ w x₁) (lift_quad φ _ w y₁) (lift_quad φ _ w hv) uv hn
    obtain ⟨v,_,ve⟩ := signed_value _ _ _ _ fin _ _ H
    exact ⟨prior_of_square _ _ _ _ _ _ hs,h,u,v,hn,he,ue,ve⟩

theorem odd_affine (X Y : K0) (h : curveC.toAffine.Nonsingular X Y) :
    RationalOddChart (.some X Y h) ↔ oddRelation X Y := by
  unfold RationalOddChart oddRelation
  simp only [WeierstrassCurve.Affine.Point.some.injEq,squareStage_iff]
  constructor
  · rintro ⟨x,y,_,⟨rfl,rfl⟩,hs⟩
    exact hs
  · exact fun hs => ⟨X,Y,h,⟨rfl,rfl⟩,hs⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.quad_square
#print axioms Sun28.Concrete.odd_rows_spec
#print axioms Sun28.Concrete.odd_affine
