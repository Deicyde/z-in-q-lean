import MinimalScalar

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic ProgressionWitnesses.SingleContact
attribute [local instance] Semiring.natCast Ring.intCast

variable {K G : Type} [Field K] [IntModule G]

structure Triple (K : Type) where
  x : K
  y : K
  z : K

def normal (t s : K) : Triple K := ⟨t,-1,s⟩
def anchor : Triple K := ⟨0,0,1⟩
def form (D : K) (a : Triple K) := a.x^3-D*a.x*a.z^2-a.y^2*a.z
def scale (k : K) (a : Triple K) : Triple K := ⟨k*a.x,k*a.y,k*a.z⟩
def flip (a : Triple K) : Triple K := ⟨a.x,-a.y,a.z⟩
def line (a b : Triple K) (T U : K) : Triple K :=
  ⟨a.x*T+b.x*U,a.y*T+b.y*U,a.z*T+b.z*U⟩

def ProperLine (a b : Triple K) := ∀ T U, line a b T U=⟨0,0,0⟩ → T=0 ∧ U=0

/-- Normalized Y-chart coordinates, the conventional inverse, and the ordinary
geometric group law on a smooth short Weierstrass cubic. The factorization
expresses intersection multiplicities for an arbitrary projective line. -/
structure CubicGeometry (D : K) (G : Type) [IntModule G] where
  point : Triple K → G
  t : G → K
  s : G → K
  origin : point (normal 0 0)=0
  read : ∀ u a, OnCurve D u a → t (point (normal u a))=u ∧ s (point (normal u a))=a
  projective : ∀ a c, form D a=0 → c≠0 → point (scale c a)=point a
  inverse : ∀ a, form D a=0 → point (flip a)= -(point a)
  three : ∀ (a b : Triple K) (i j k l m n c : K), ProperLine a b → c≠0 →
    (i≠0 ∨ j≠0) → (k≠0 ∨ l≠0) → (m≠0 ∨ n≠0) →
    (∀ T U, form D (line a b T U)=c*(j*T-i*U)*(l*T-k*U)*(n*T-m*U)) →
    point (line a b i j)+point (line a b k l)+point (line a b m n)=0

variable {D : K} (C : CubicGeometry D G)

/-- The actual projective point is in the normalized Y patch. -/
def CubicGeometry.defined (Q : G) := OnCurve D (C.t Q) (C.s Q) ∧ C.point (normal (C.t Q) (C.s Q))=Q

private theorem normal_form {u s : K} (h : OnCurve D u s) : form D (normal u s)=0 := by
  dsimp [form,normal];unfold OnCurve at h;grobner

private theorem represented {Q : G} {u s : K} (h : OnCurve D u s) (read : C.point (normal u s)=Q) :
    C.defined Q ∧ C.t Q=u ∧ C.s Q=s := by
  obtain ⟨t,v⟩:=C.read _ _ h
  rw [read] at t v
  exact ⟨⟨by rwa [t,v],by rwa [t,v]⟩,t,v⟩

private theorem minus_one_live : (-1:K)≠0 := by
  intro z;apply Field.zero_ne_one (α:=K);grobner

private theorem reflected {u s : K} (h : OnCurve D u s) :
    C.point (normal (-u) (-s))= -C.point (normal u s) := by
  have he := normal_form h
  have hf : form D (flip (normal u s))=0 := by dsimp [form,flip,normal] at he ⊢;grobner
  have scaled:=C.projective (flip (normal u s)) (-1) hf minus_one_live
  have triple : scale (-1) (flip (normal u s))=normal (-u) (-s) := by
    unfold flip normal scale;congr 1 <;> grobner
  rw [triple] at scaled
  exact scaled.trans (C.inverse _ he)

private theorem third {a b c : G} (h : a+b+c=0) : a+b= -c := by
  have e:=congrArg (· + -c) h
  change ((a+b)+c)+(-c)=0+(-c) at e
  rwa [AddCommMonoid.add_assoc (a+b) c (-c),AddCommGroup.add_neg_cancel,AddCommMonoid.add_zero,AddCommMonoid.zero_add] at e

private theorem regular_line (l k : K) (T U : K) :
    line (⟨1,0,l⟩ : Triple K) ⟨0,-1,k⟩ T U=⟨T,-U,l*T+k*U⟩ := by
  dsimp [line];congr 1 <;> grobner

def CubicGeometry.model : ProjectiveGroup D G where
  t:=C.t
  s:=C.s
  defined:=C.defined
  origin:=represented C (by unfold OnCurve;grobner) C.origin
  equation:=fun _ h=>h.1
  atInfinity:=by
    intro Q h t s
    have e:=h.2
    rw [t,s,C.origin] at e
    exact e.symm
  reflect:=by
    intro Q q
    apply represented C
    · have h:=q.1;unfold OnCurve at h ⊢;grobner
    · rw [reflected C q.1,q.2]
  sum:=by
    intro P Q l k h pd qd pa qb cert
    let a : Triple K:=⟨1,0,l⟩
    let b : Triple K:=⟨0,-1,k⟩
    have independent : ProperLine a b := by
      intro T U eq
      rw [regular_line] at eq
      have t:=congrArg Triple.x eq;have u:=congrArg Triple.y eq
      exact ⟨t,by change -U=0 at u;grobner⟩
    have h1 : (1:K)≠0 := fun e=>Field.zero_ne_one e.symm
    have roots:=C.three a b (C.t P) 1 (C.t Q) 1 (-h) 1 (leading D l) independent cert.1
      (Or.inr h1) (Or.inr h1) (Or.inr h1) (by
        intro T U
        rw [regular_line]
        dsimp [form]
        have e:=cert.2 T U
        grobner)
    have param (u : K) : line a b u 1=normal u (l*u+k) := by rw [regular_line];dsimp [normal];congr 1;grobner
    rw [param,param,param,←pa,←qb,pd.2,qd.2] at roots
    have h3:=third_on_curve cert
    have hneg : OnCurve D (-h) (l*(-h)+k) := by unfold OnCurve at h3 ⊢;grobner
    have re:=reflected C hneg
    rw [show - -h=h by grobner,show -(l*(-h)+k)=l*h-k by grobner] at re
    exact represented C h3 (re.trans (third roots).symm)

private theorem anchor_line (t T U : K) :
    line (⟨t,-1,0⟩ : Triple K) ⟨0,0,1⟩ T U=⟨t*T,-T,U⟩ := by
  dsimp [line];congr 1 <;> grobner

def CubicGeometry.zeroAnchor : ZeroAnchor C.model where
  T:=C.point anchor
  twice:=by
    have h:=C.inverse anchor (by dsimp [anchor,form];grobner)
    have flip0 : flip (anchor (K:=K))=anchor := by dsimp [flip,anchor];congr 1;grobner
    rw [flip0] at h
    rw [show (2:Int)=1+1 by decide,IntModule.add_zsmul,IntModule.one_zsmul,←AddCommGroup.sub_self (C.point anchor)]
    rw [AddCommGroup.sub_eq_add_neg,←h]
  line:=by
    intro Q v q cert
    let t:=C.t Q
    let s:=C.s Q
    let a : Triple K:=⟨t,-1,0⟩
    let b : Triple K:=⟨0,0,1⟩
    have independent : ProperLine a b := by
      intro T U eq
      rw [anchor_line] at eq
      have e:=congrArg Triple.y eq
      exact ⟨by change -T=0 at e;grobner,congrArg Triple.z eq⟩
    have live : -(D*t)≠0 := by intro z;apply cert.1;change D*t=0;grobner
    have h1 : (1:K)≠0 := fun e=>Field.zero_ne_one e.symm
    have roots:=C.three a b 1 s 0 1 1 v (-(D*t)) independent live
      (Or.inl h1) (Or.inr h1) (Or.inl h1) (by
        intro T U
        rw [anchor_line]
        dsimp [form]
        have e:=cert.2 T U
        change T^2*U-t^3*T^3+D*t*T*U^2 =D*t*T*(U-s*T)*(U-v*T) at e
        grobner)
    have finite (u : K) : line a b 1 u=normal t u := by rw [anchor_line];dsimp [normal];congr 1;grobner
    have atT : line a b 0 1=anchor := by rw [anchor_line];dsimp [anchor];congr 1 <;> grobner
    rw [finite,atT,finite,q.2] at roots
    have e:=cert.2 1 v
    have vcurve : OnCurve D t v := by
      change (1:K)^2*v-t^3*1^3+D*t*1*v^2=D*t*1*(v-s*1)*(v-v*1) at e
      unfold OnCurve;grobner
    have target : OnCurve D (-t) (-v) := by unfold OnCurve at vcurve ⊢;grobner
    exact represented C target ((reflected C vcurve).trans (third roots).symm)

end ProjectionFibres
