import MixedChart

namespace WitnessTransfer
open Lean.Grind FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast

/-- The four elementary laws needed of an inclusion or a residue map. -/
structure RingMap (O K : Type) [CommRing O] [CommRing K] where
  map : O → K
  add : ∀ x y,map (x+y)=map x+map y
  mul : ∀ x y,map (x*y)=map x*map y
  int : ∀ i : Int,map (i:O)=(i:K)

namespace RingMap
variable {O K : Type} [CommRing O] [CommRing K]
theorem zero (h : RingMap O K) : h.map 0=0 := by simpa only [Ring.intCast_zero] using h.int 0
theorem one (h : RingMap O K) : h.map 1=1 := by simpa only [Ring.intCast_one] using h.int 1
theorem sub (h : RingMap O K) (a b) : h.map (a-b)=h.map a-h.map b := by
  have hh:=h.add (a-b) b
  rw [show a-b+b=a from by grobner] at hh;grobner
theorem pow (h : RingMap O K) (a) (n : Nat) : h.map (a^n)=(h.map a)^n := by
  induction n with
  | zero => rw [Semiring.pow_zero,Semiring.pow_zero,h.one]
  | succ n ih => rw [Semiring.pow_succ,Semiring.pow_succ,h.mul,ih]

def jet (h : RingMap O K) : (n : Nat) → J O n → J K n
  | 0, _ => ()
  | n+1, a => (h.map a.1,jet h n a.2)

theorem jet_inj (h : RingMap O K) (inj : Function.Injective h.map) (n) : Function.Injective (h.jet n) := by
  induction n with
  | zero => exact fun {a b} _=>@Subsingleton.elim Unit inferInstance a b
  | succ n ih =>
    intro a b eq
    exact Prod.ext (inj (congrArg Prod.fst eq)) (ih (congrArg Prod.snd eq))

theorem jet_plus (h : RingMap O K) (n) (a b : J O n) :
    h.jet n (plus n a b)=plus n (h.jet n a) (h.jet n b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (h.add ..) (ih ..)

theorem jet_scale (h : RingMap O K) (n) (s : O) (a : J O n) :
    h.jet n (scale n s a)=scale n (h.map s) (h.jet n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (h.mul ..) (ih ..)

theorem jet_cut (h : RingMap O K) (n) (a : J O (n+1)) :
    h.jet n (cut n a)=cut n (h.jet (n+1) a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih a.2)

theorem jet_times (h : RingMap O K) (n) (a b : J O n) :
    h.jet n (times n a b)=times n (h.jet n a) (h.jet n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (h.mul ..) ?_
    change h.jet n (plus n (scale n a.1 b.2) (times n a.2 (cut n b)))=_
    rw [jet_plus,jet_scale,ih,jet_cut];rfl

theorem jet_plug (h : RingMap O K) (n) (a b : J O n) :
    h.jet n (plug n a b)=plug n (h.jet n a) (h.jet n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change h.jet n (times n (cut n a) (plug n (cut n a) b.2))=_
    rw [jet_times,ih,jet_cut];rfl
end RingMap

variable {O : Type} [CommRing O]
def horner (z : O) : (n : Nat) → J O n → O
  | 0, _ => 0
  | n+1, a => a.1+z*horner z n a.2

theorem horner_scale (z : O) (n) (b : O) (a : J O n) :
    horner z n (scale n b a)=b*horner z n a := by
  induction n with
  | zero => simp only [horner];grobner
  | succ n ih => simp only [horner,scale,ih];grobner

/-- Integral remainders of two Taylor evaluations. -/
def expands (n) (z v : O) (a : J O n) : Prop := ∃ r : O,v=horner z n a+z^n*r

/-- Characteristic-zero cancellation happens before passing to the valuation
ring. Even when a prime divides 2^i−2, the extracted remainder is integral. -/
theorem integral_multiple {K : Type} [Field K] [IsCharP K 0]
    (incl : RingMap O K) (injective : Function.Injective incl.map) (c : Parameter)
    (f : CurveData K (4*c.k)) (m j : J O (4*c.k+1)) (b : Int) (z v vb : O)
    (slope : coeff _ (incl.jet _ m) 0=(b:K))
    (law : commutes _ (incl.jet _ m) f.dup)
    (chart : val f.w c.q*(incl.jet _ j)=X (4*c.k+1)*val f.w c.a)
    (single : expands (4*c.k+1) z v j) (multiple : expands (4*c.k+1) z vb (plug _ m j)) :
    ∃ r : O,vb-(b:O)*v=z^(4*c.k+1)*r := by
  have eq := physical_multipliers c f (incl.jet _ j) (incl.jet _ m) (b:K) slope law chart
  have lifted : plug _ m j=scale _ (b:O) j := incl.jet_inj injective _ (by rw [incl.jet_plug,incl.jet_scale,incl.int,eq])
  obtain ⟨a,ha⟩:=single
  obtain ⟨e,he⟩:=multiple
  rw [lifted,horner_scale] at he
  exact ⟨e-(b:O)*a,by rw [ha,he];grobner⟩

#print axioms integral_multiple
end WitnessTransfer
