import LocalRatio

namespace WitnessTransfer
open Lean.Grind FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast
variable {O K : Type} [CommRing O] [CommRing K]

namespace RingMap
theorem jet_con (h : RingMap O K) (n) (c : O) : h.jet n (con n c)=con n (h.map c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change h.jet n (con n 0)=con n 0
    rw [ih,h.zero]

theorem jet_X (h : RingMap O K) (n) : h.jet n (X n)=X n := by
  cases n with
  | zero => rfl
  | succ n => exact Prod.ext h.zero ((h.jet_con n 1).trans (congrArg (con n) h.one))

theorem jet_num (h : RingMap O K) (n r : Nat) :
    h.jet n (OfNat.ofNat (α:=J O n) r)=OfNat.ofNat (α:=J K n) r := by
  change h.jet n (con n (r:O))=con n (r:K)
  rw [jet_con,show h.map (r:O)=(r:K) from by simpa only [Ring.intCast_natCast] using h.int (r:Int)]

def onJets (h : RingMap O K) (n) : RingMap (J O n) (J K n) where
  map:=h.jet n
  add:=h.jet_plus n
  mul:=h.jet_times n
  int:=fun i=>by change h.jet n (con n (i:O))=con n (i:K);rw [jet_con,h.int]

theorem val_map (h : RingMap O K) (v : O) (a : Poly) : h.map (val v a)=val (h.map v) a := by
  induction a with
  | nil => exact h.zero
  | cons i a ih => change h.map ((i:O)+v*val v a)=_;rw [h.add,h.mul,h.int,ih];rfl

def curve (h : RingMap O K) {n} (f : CurveData O n) : CurveData K n := by
  let v:=h.onJets (n+1)
  have num (j : Nat) : v.map (OfNat.ofNat (α:=J O (n+1)) j)=OfNat.ofNat (α:=J K (n+1)) j := h.jet_num _ j
  refine ⟨h.map f.D, h.jet _ f.w, h.jet _ f.dup,?_,?_,?_⟩
  · have eq:=congrArg v.map f.curve
    rw [v.mul,v.mul,v.pow,v.pow,v.sub,show v.map (X _)=X _ from h.jet_X _,
       show v.map (con _ f.D)=con _ (h.map f.D) from h.jet_con ..,num 1] at eq
    exact eq
  · have eq:=congrArg v.map f.doubleW
    rw [v.mul,v.pow,v.add,num 1,v.mul,v.mul,v.pow,v.sub,num 1,num 16,
      show v.map (plug _ f.dup f.w)=plug _ (v.map f.dup) (v.map f.w) from h.jet_plug ..] at eq
    exact eq
  · have eq:=congrArg v.map f.doubleZ
    rw [v.mul,v.add,v.sub,v.mul,v.pow,num 1,num 6,v.mul,v.sub,v.pow,num 1,num 2] at eq
    exact eq
end RingMap

/-- The actual characteristic-zero chart has an integral representative when
the curve coefficient comes from O and the indicated integer is a local unit. -/
theorem integral_representative (h : RingMap O K) (c : Parameter) {n} (D : O) (f : CurveData K n)
    (good : unit ((c.q.head?.getD 0:Int):O)) (parameter : h.map D=f.D) :
    ∃ j : J O (n+1),val f.w c.q*(h.jet _ j)=X (n+1)*val f.w c.a := by
  obtain ⟨g,hD⟩:=curve_exists n D
  obtain ⟨j,hj,_⟩:=integral_chart_exists c g good
  have same : (h.curve g).D=f.D := by change h.map g.D=f.D; rw [hD,parameter]
  have hw : h.jet _ g.w=f.w := (curve_unique (h.curve g) f same).1
  let v:=h.onJets (n+1)
  have eq:=congrArg v.map hj
  rw [v.mul,v.mul,v.val_map,v.val_map,show v.map (X _)=X _ from h.jet_X _,show v.map g.w=f.w from hw] at eq
  exact ⟨j,eq⟩

private def leading : Parameter→Nat | .raw=>1 | .short=>15 | .pade=>515764275

/-- These are exactly the six primes in the three physical rational chart constants. -/
theorem denominator_factors : (515764275:Nat)=3*5^2*13*17*29^2*37 := by decide

theorem good_denominators {p : Nat} {F : Type} [Field F] [IsCharP F p]
    (place : Local.Place O F) (off : ¬p∣515764275) (c : Parameter) :
    unit ((c.q.head?.getD 0:Int):O) := by
  have h : c.q.head?.getD 0=(leading c:Int) := by cases c <;> decide
  have d : leading c ∣ 515764275 := by cases c <;> decide
  apply place.liftUnit
  rw [place.residue.int,h,Ring.intCast_natCast]
  intro eq
  have div := Nat.dvd_of_mod_eq_zero ((IsCharP.natCast_eq_zero_iff (α:=F) p _).mp eq)
  exact off (Nat.dvd_trans div d)

/-- At a formal point the actual rational factor J(z)/z reduces to one,
also when the numerator point is the identity. -/
theorem unit_chart_value {p : Nat} {F : Type} [Field F] [IsCharP F p]
    (place : Local.Place O F) (off : ¬p∣515764275) (c : Parameter) (w a : O)
    (formal : place.residue.map w=0) (value : val w c.q*a=val w c.a) :
    place.residue.map a=1 ∧ unit a := by
  have leadQ : c.q.head?.getD 0=(leading c:Int) := by cases c <;> decide
  have leadA : c.a.head?.getD 0=(leading c:Int) := by cases c <;> decide
  have ev0 (q : Poly) : val (0:F) q=((q.head?.getD 0:Int):F) := by
    cases q with
    | nil => change (0:F)=((0:Int):F);rw [Ring.intCast_zero]
    | cons i t => change (i:F)+0*val 0 t=(i:F);grobner
  have h:=congrArg place.residue.map value
  rw [place.residue.mul,place.residue.val_map,place.residue.val_map,formal,ev0,ev0,leadQ,leadA] at h
  have d : leading c ∣ 515764275 := by cases c <;> decide
  have nz : ((leading c:Int):F)≠0 := by
    rw [Ring.intCast_natCast]; intro e
    exact off (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ((IsCharP.natCast_eq_zero_iff (α:=F) p _).mp e)) d)
  have ha:=cancel_unit ⟨_,Field.inv_mul_cancel nz⟩
    (show ((leading c:Int):F)*place.residue.map a=((leading c:Int):F)*1 from by rw [h];grobner)
  exact ⟨ha,place.liftUnit a (fun zero=>by rw [ha] at zero;exact Field.zero_ne_one zero.symm)⟩

theorem nonzero_reference {F : Type} [Field F] (h : RingMap O F)
    (inj : Function.Injective h.map) (y : O) (hy : y≠0) :
    ∀ a b : O,y*a=y*b → a=b := by
  intro a b eq
  have nz : h.map y≠0 := fun ey=>hy (inj (ey.trans h.zero.symm))
  have e:=congrArg h.map eq
  rw [h.mul,h.mul] at e
  exact inj (cancel_unit ⟨_,Field.inv_mul_cancel nz⟩ e)

#print axioms unit_chart_value
#print axioms nonzero_reference
#print axioms integral_representative
#print axioms denominator_factors
#print axioms good_denominators
end WitnessTransfer
