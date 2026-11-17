import LocalRatio

namespace WitnessTransfer.Local
open Lean.Grind IndependentIndices
attribute [local instance] Semiring.natCast Ring.intCast
variable {O F R : Type} [CommRing O] [Field F] [CommRing R]

private theorem prime_power (p k : Nat) [IsCharP R (p^k)] : (p:R)^k=0 := by
  rw [← Semiring.natCast_pow]
  exact (IsCharP.natCast_eq_zero_iff (α:=R) (p^k) (p^k)).mpr (Nat.mod_self _)

private theorem map_nat (red : RingMap O R) (p : Nat) : red.map (p:O)=(p:R) := by
  simpa only [Ring.intCast_natCast] using red.int (p:Int)

theorem vanishes (p k e d : Nat) [IsCharP R (p^k)] (red : RingMap O R) (y : O)
    (depth : ∃ v : O,y=(p:O)^e*v) (enough : k≤e*d) : red.map (y^d)=0 := by
  obtain ⟨v,hv⟩:=depth
  rw [red.pow,hv,red.mul,red.pow,map_nat,CommSemiring.mul_pow,pow_power]
  rw [show e*d=k+(e*d-k) from by omega,Semiring.pow_add,prime_power p k]
  grobner

theorem reduce_multiple (p k e d : Nat) [IsCharP R (p^k)] (red : RingMap O R)
    (s : Side O) (m a : Int) (obs : AtMultiple s m a d)
    (depth : ∃ v : O,s.y=(p:O)^e*v) (enough : k≤e*d) {l : O} (ok : ratio s l) :
    (m:R)*red.map l=(a:R) := by
  obtain ⟨r,hr⟩:=cancel_reference s obs ok
  obtain ⟨v,hv⟩:=s.ry_unit
  have h1:=congrArg red.map hv
  change red.map (v*s.ry)=red.map 1 at h1
  rw [red.mul,red.one] at h1
  have hm:=congrArg red.map hr
  change red.map (s.ry*((m:O)*l-(a:O)))=red.map (s.y^d*r) at hm
  rw [red.mul,red.sub,red.mul,red.int,red.int,red.mul,vanishes p k e d red s.y depth enough] at hm
  have h : red.map s.ry*((m:R)*red.map l-(a:R))=red.map s.ry*0 := by rw [hm];grobner
  have h2:=cancel_unit ⟨_,h1⟩ h
  grobner

def precision (short : Bool) : Nat := if short then 10 else 40
def alternateOrder (short : Bool) : Nat := if short then 12 else 40

/-- A single physical comparison. The multiple observations refer to group
values and absolute Taylor remainders at the actual four source points. -/
structure Observation (O : Type) [CommRing O] (p : Nat) (short : Bool) (m n : Int) where
  primary : Side O
  alternate : Side O
  u : Int
  firstTangent : Tangent primary m (2*u)
  secondTangent : Tangent alternate (m-2) (2*(u-n))
  firstValue : AtMultiple primary m (2*u) 4
  secondValue : AtMultiple alternate (m-2) (2*(u-n)) (alternateOrder short)
  firstDepth : ∃ v : O,primary.y=(p:O)^20*v
  secondDepth : ∃ v : O,alternate.y=(p:O)^1*v
  crossError : O
  cross : crossEq primary alternate ((p:O)^(precision short)*crossError)

theorem observed_row (p : Nat) (short : Bool) {m n : Int}
    [IsCharP R (p^(precision short))] (place : Place O F) (red : RingMap O R)
    (a : Observation O p short m n)
    (sx : place.residue.map a.primary.x=0) (tx : place.residue.map a.alternate.x=0) :
    ∃ (r : LogRow R m n) (l : O),ratio a.primary l ∧ r.primary=red.map l := by
  obtain ⟨l,l',hl,hl',cross⟩:=two_sides place a.primary a.alternate m a.u n sx tx
    a.firstTangent a.secondTangent _ a.cross
  have h1:=reduce_multiple p (precision short) 20 4 red a.primary m (2*a.u)
    a.firstValue a.firstDepth (by cases short <;> decide) hl
  have h2:=reduce_multiple p (precision short) 1 (alternateOrder short) red a.alternate (m-2) (2*(a.u-n))
    a.secondValue a.secondDepth (by cases short <;> decide) hl'
  have hc:=congrArg red.map cross
  change red.map (l-l')=red.map (_*a.crossError) at hc
  rw [red.sub,red.mul,red.pow,map_nat,prime_power] at hc
  have two : ((2:Int):R)=(2:R) := Ring.intCast_ofNat 2
  simp only [Ring.intCast_sub,Ring.intCast_mul,two] at h1 h2
  exact ⟨⟨a.u,red.map l,red.map l',by grobner,h1,h2⟩,l,hl,rfl⟩

/-- Each private contact has four physical ratios; equations on their reductions
are the literal detector and Lucas tests. -/
theorem observed_contact (p : Nat) (m : Int) (ns : Labels) (B : Rat) (odd : p%2=1)
    (o : Place O F) (r10 : Residue (p^10)) (r40 : Residue (p^40))
    (red10 : @RingMap O r10.carrier _ r10.ring) (red40 : @RingMap O r40.carrier _ r40.ring)
    (a : Observation O p true m ns.n₁) (b : Observation O p false m ns.n₂)
    (c : Observation O p false m ns.n₃) (d : Observation O p false m ns.n₄)
    (za : o.residue.map a.primary.x=0 ∧ o.residue.map a.alternate.x=0)
    (zb : o.residue.map b.primary.x=0 ∧ o.residue.map b.alternate.x=0)
    (zc : o.residue.map c.primary.x=0 ∧ o.residue.map c.alternate.x=0)
    (zd : o.residue.map d.primary.x=0 ∧ o.residue.map d.alternate.x=0)
    (detector : letI := r10.ring; ∀ l,ratio a.primary l → (B.den:r10.carrier)*red10.map l=(B.num:r10.carrier))
    (test : letI := r40.ring; ∀ x y z,ratio b.primary x → ratio c.primary y → ratio d.primary z →
      IndependentIndices.lucas (red40.map x) (red40.map y) (red40.map z)=0) :
    Nonempty (Contact p m ns B) := by
  letI := r10.ring
  letI := r10.characteristic
  letI := r40.ring
  letI := r40.characteristic
  obtain ⟨r,x,hx,rx⟩:=observed_row p true o red10 a za.1 za.2
  obtain ⟨s,y,hy,sy⟩:=observed_row p false o red40 b zb.1 zb.2
  obtain ⟨t,z,hz,tz⟩:=observed_row p false o red40 c zc.1 zc.2
  obtain ⟨v,w,hw,vw⟩:=observed_row p false o red40 d zd.1 zd.2
  exact ⟨⟨odd,r10,r40,r,s,t,v,by rw [rx];exact detector x hx,by rw [sy,tz,vw];exact test y z w hy hz hw⟩⟩

#print axioms two_sides
#print axioms cancel_reference
#print axioms observed_row
#print axioms observed_contact
end WitnessTransfer.Local
