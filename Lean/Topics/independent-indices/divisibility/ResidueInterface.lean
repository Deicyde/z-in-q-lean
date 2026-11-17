import LocalFractions

namespace IndependentIndices
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

def halfIndex {R : Type} [CommRing R] (N : Nat) (m : Int) : R := (m:R)*(((N+1)/2:Nat):R)

theorem half_index_spec {R : Type} [CommRing R] (N : Nat) [IsCharP R N] (odd : N%2=1) (m : Int) :
    2*halfIndex (R:=R) N m=(m:R) ∧ 2*(halfIndex (R:=R) N m-1)=(m:R)-2 := by
  have h:=two_unit (R:=R) odd
  unfold halfIndex;constructor <;> grobner

theorem half_log_iff {R : Type} [CommRing R] (N : Nat) [IsCharP R N] (odd : N%2=1) (m u n : Int) (l l' : R) :
    ((m:R)*l=2*(u:R) ∧ ((m:R)-2)*l'=2*((u:R)-(n:R))) ↔
    (halfIndex (R:=R) N m*l=(u:R) ∧ (halfIndex (R:=R) N m-1)*l'=(u:R)-(n:R)) := by
  obtain ⟨a,b⟩:=half_index_spec (R:=R) N odd m
  have unit:=two_unit (R:=R) odd
  constructor
  · rintro ⟨x,y⟩
    have cancel (z w : R) (eq : 2*z=2*w) : z=w := by
      have hm:=congrArg (fun r : R=>r*(((N+1)/2:Nat):R)) eq
      grobner
    constructor <;> apply cancel <;> grobner
  · rintro ⟨x,y⟩;constructor <;> grobner

private theorem bezout (a b : Nat) :
    ∃ i j : Int, ((Nat.gcd a b:Nat):Int)=(a:Int)*i+(b:Int)*j := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases h : a=0
    · subst a;exact ⟨0,1,by simp⟩
    · obtain ⟨i,j,hij⟩:=ih (b%a) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) a
      have eq:=congrArg (fun n : Nat=>(n:Int)) (Nat.mod_add_div b a)
      simp only [Int.natCast_add,Int.natCast_mul] at eq
      refine ⟨j-(b/a:Int)*i,i,?_⟩
      rw [Nat.gcd_def,if_neg h,hij]
      grobner

theorem inverse_denominator {R : Type} [CommRing R] (N d : Nat) [IsCharP R N]
    (coprime : d.Coprime N) : ∃ inv : R,(d:R)*inv=1 := by
  obtain ⟨i,j,eq⟩:=bezout d N
  rw [coprime.gcd_eq_one] at eq
  have z : ((N:Int):R)=0 := (integer_zero _).mpr (Int.dvd_refl _)
  have h:=congrArg (fun n : Int=>(n:R)) eq
  simp only [Ring.intCast_add,Ring.intCast_mul,Ring.intCast_natCast] at h z
  refine ⟨(i:R),?_⟩
  have h1 : ((1:Nat):R)=1 := Semiring.natCast_one
  grobner

def reducedImage {R : Type} [CommRing R] (x : Rat) (z : R) := (x.den:R)*z=(x.num:R)

theorem reduced_image_unique {R : Type} [CommRing R] (N : Nat) [IsCharP R N] (x : Rat)
    (coprime : x.den.Coprime N) : ∃ z : R, reducedImage x z ∧ ∀ y : R,reducedImage x y → y=z := by
  obtain ⟨inv,ok⟩:=inverse_denominator (R:=R) N x.den coprime
  refine ⟨(x.num:R)*inv,?_,?_⟩
  · unfold reducedImage;grobner
  · intro y hy;unfold reducedImage at hy;grobner

/-- Concrete split-place specialization on the actual modular integer rings. -/
theorem finite_place (p : Nat) [NeZero (p^10)] [NeZero (p^40)] (odd : p%2=1) {m ns B}
    (rows : Ratios (Fin (p^10)) (Fin (p^40)) m ns B) : Defects p ns B ∧ B.den.Coprime (p^10) := by
  have h:=local_divisibilities p odd rows
  exact ⟨h,detector_denominator h.2⟩

theorem lucas_source (a t b : Int) : lucas a t b=t^2-a*(a-2)*t*b+(a-2)^2*b^2-1 := by
  unfold lucas;grobner

def empty_frame (ns : Labels) (B : Rat) (m : Int) : Frame ns B :=
  ⟨m,[],by simp⟩

theorem largest_is_observed (a b c : Nat) :
    largest a b c=a ∨ largest a b c=b ∨ largest a b c=c := by
  apply three_max (P:=fun j=>j=a ∨ j=b ∨ j=c) <;> simp

/-- The source comparison heights can all be evaluated against the largest radical. -/
theorem common_bound {T : Type} (bound : Nat→T→Prop) (mono : ∀ {a b z},a≤b→bound a z→bound b z)
    (a b c : Nat) (x y z : T) (hx : bound a x) (hy : bound b y) (hz : bound c z) :
    bound (largest a b c) x ∧ bound (largest a b c) y ∧ bound (largest a b c) z := by
  obtain ⟨ha,hb,hc⟩:=largest_bounds a b c
  exact ⟨mono ha hx,mono hb hy,mono hc hz⟩

end IndependentIndices
