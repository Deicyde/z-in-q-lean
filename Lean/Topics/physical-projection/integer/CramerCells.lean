import AffineRows
import DetectorCells
import PadeRecovery
namespace Physical130
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data CircuitTransport PhysicalProjection

def blindLine (j : Nat) (p : Polynomial) : Bool :=
  reads (apart padeSlots) (column j .c p) && reads (apart padeSlots) (column j .u p) && reads (apart padeSlots) (column j .v p)

theorem blind_matrices (k : PPair) : blindLine k.slot k.f=true ∧ blindLine k.slot k.g=true := by cases k <;> decide

theorem column_agree {j p x z} (h : blindLine j p=true) (offZ : off padeSlots x z) (part : Column) :
    value z (column j part p)=value x (column j part p) := by
  simp only [blindLine,Bool.and_eq_true] at h
  apply agree_off offZ;apply reads_supported
  cases part with | c => exact h.1.1 | u => exact h.1.2 | v => exact h.2

theorem placement {j p x z} (h : blindLine j p=true) (offZ : off padeSlots x z) :
    value z p = value x (column j .c p) + z j*value x (column j .u p)+z (j+1)*value x (column j .v p) := by
  rw [split_value z j p,column_agree h offZ .c,column_agree h offZ .u,column_agree h offZ .v]

private theorem columns (gate : Bool) (k : PPair) (z : ProjectionDescent.Assignment) (ok : pivotOK gate z)
    (p : Polynomial) (blind : blindLine k.slot p=true) (a b : Rat)
    (affine : ∀ w, pivotOK gate w → off padeSlots z w →
      value w p=value (k.blank z) p + a*w k.slot+b*w (k.slot+1)) :
    value z (column k.slot .u p)=a ∧ value z (column k.slot .v p)=b := by
  have tags : k.slot∈padeSlots ∧ k.slot+1∈padeSlots := by cases k <;> decide
  have eqn (u v : Rat) : value z (column k.slot .c p)+u*value z (column k.slot .u p)+v*value z (column k.slot .v p)
      = value (k.blank z) p+a*u+b*v := by
    let w:=put (put z k.slot u) (k.slot+1) v
    have offZ : off padeSlots z w := by
      intro i hi; have h1 : i≠k.slot := fun h => hi (h ▸ tags.1)
      have h2 : i≠k.slot+1 := fun h => hi (h ▸ tags.2)
      simp [w,put,h1,h2]
    have l : w k.slot=u := by simp [w,put]
    have r : w (k.slot+1)=v := by simp [w,put]
    have left:=placement blind offZ
    have right:=affine w (matrix_blind gate ok offZ) offZ
    rw [left,l,r] at right;exact right
  have h0:=eqn 0 0;have h1:=eqn 1 0;have h2:=eqn 0 1
  constructor <;> grobner

theorem matrix_columns (gate : Bool) (k : PPair) (z : ProjectionDescent.Assignment) (ok : pivotOK gate z) :
    (value z (column k.slot .u k.f)=k.A z ∧ value z (column k.slot .v k.f)=2*k.B z) ∧
    (value z (column k.slot .u k.g)=k.B z ∧ value z (column k.slot .v k.g)=k.A z) := by
  have supp {w : ProjectionDescent.Assignment} (h : off padeSlots z w) : ∀ i∈k.support, w i=z i := by
    intro i hi; have hv := pair_support_visible k i hi
    exact h i (by simp [visible,apart] at hv;exact hv.2)
  have ab {w : ProjectionDescent.Assignment} (h : off padeSlots z w) : k.A w=k.A z ∧ k.B w=k.B z := by
    have l:=supp h k.xslot (by simp [PPair.support])
    have r:=supp h (k.xslot+1) (by simp [PPair.support])
    simp only [PPair.A,PPair.B,PPair.w0,PPair.w1,l,r,and_self]
  constructor
  · apply columns gate k z ok k.f (blind_matrices k).1
    intro w h offW;rw [pade_f gate k w h,(blank_agree k (supp offW)).1,(ab offW).1,(ab offW).2]
  · apply columns gate k z ok k.g (blind_matrices k).2
    intro w h offW;rw [pade_g gate k w h,(blank_agree k (supp offW)).2,(ab offW).1,(ab offW).2]

def det4 (b : Book) (a c d e : Word) := plus b (times b a e) (negWord b (times b c d))

theorem det_value (b : Book) (x : ProjectionDescent.Assignment) (a c d e : Word) :
    (det4 b a c d e).value b x=a.value b x*e.value b x-c.value b x*d.value b x := by
  simp only [det4,plus_value,times_value,neg_value];grobner

structure Triple where
  d : Word
  u : Word
  v : Word

def cramerFrom (b : Book) (f g : Aff) : Triple :=
  ⟨det4 b f.u f.v g.u g.v,det4 b (negWord b f.c) f.v (negWord b g.c) g.v,
   det4 b f.u (negWord b f.c) g.u (negWord b g.c)⟩

def cramer (b : Book) (env : Coords) (k : PPair) :=
  cramerFrom b (line b env k.slot k.f) (line b env k.slot k.g)

structure CramerCorrect (b : Book) (x z : ProjectionDescent.Assignment) (k : PPair) (t : Triple) : Prop where
  nonzero : t.d.value b x≠0
  u : t.u.value b x=t.d.value b x*z k.slot
  v : t.v.value b x=t.d.value b x*z (k.slot+1)

theorem rat_den_ne (n : Nat) (hn : 0<n) : (n:Rat)≠0 :=
  fun eq => (Nat.ne_of_gt hn) (Rat.natCast_eq_zero_iff.mp eq)

theorem cramer_scale {book env gate} (y : Fin 130→Rat) (k : PPair)
    (al : Along book (finiteLift y) env (middle gate y)) :
    (cramer book env k).d.value book (finiteLift y)=
      ((line book env k.slot k.f).den:Rat)*((line book env k.slot k.g).den:Rat)*k.det (middle gate y) := by
  have hf:=line_correct al k.slot k.f;have hg:=line_correct al k.slot k.g
  have cm:=matrix_columns gate k (middle gate y) (all_solved (ps gate) (good0 gate) _)
  change (det4 _ _ _ _ _).value _ _=_
  rw [det_value,hf.u,hf.v,hg.u,hg.v,cm.1.1,cm.1.2,cm.2.1,cm.2.2];unfold PPair.det;grobner

theorem cramer_correct {book env gate} (y : Fin 130→Rat) (k : PPair)
    (al : Along book (finiteLift y) env (middle gate y)) :
    CramerCorrect book (finiteLift y) (chartPoint gate y) k (cramer book env k) := by
  let m:=middle gate y;let z:=chartPoint gate y;let x:=finiteLift y
  let f:=line book env k.slot k.f; let g:=line book env k.slot k.g
  have hf:=line_correct al k.slot k.f;have hg:=line_correct al k.slot k.g
  have eqD : (cramerFrom book f g).d.value book x=(f.den:Rat)*(g.den:Rat)*k.det m := cramer_scale y k al
  have offW : off padeSlots m z := fun i hi => fillPairs_keep _ hi
  have equation (p : Polynomial) (l : Aff) (a : AffCorrect book x m k.slot p l) (blind : blindLine k.slot p=true)
      (sol : value z p=0) : l.c.value book x+l.u.value book x*z k.slot+l.v.value book x*z (k.slot+1)=0 := by
    rw [a.c,a.u,a.v];rw [placement blind offW] at sol;grobner
  have eqf:=equation k.f f hf (blind_matrices k).1 (point_pade gate y k).1
  have eqg:=equation k.g g hg (blind_matrices k).2 (point_pade gate y k).2
  change CramerCorrect book x z k (cramerFrom book f g)
  constructor
  · rw [eqD]; intro h
    have hh:=(Rat.mul_eq_zero.mp h).resolve_right (pair_det_ne k m)
    exact (rat_den_ne _ hg.pos) ((Rat.mul_eq_zero.mp hh).resolve_left (rat_den_ne _ hf.pos))
  · change (det4 _ _ _ _ _).value _ _=(det4 _ _ _ _ _).value _ _*_
    simp only [det_value,neg_value];grobner
  · change (det4 _ _ _ _ _).value _ _=(det4 _ _ _ _ _).value _ _*_
    simp only [det_value,neg_value];grobner

end Physical130
