import Commuting

namespace WitnessTransfer.FiniteJet
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type} [CommRing R]

private theorem exchange (n) (a b c : J R n) :
    plus n a (plus n b c)=plus n b (plus n a c) := by
  rw [← plus_assoc,plus_comm (R:=R) n a b,plus_assoc]

private theorem right_tail (n) (a b : J R (n+1)) :
    (times (n+1) a b).2=plus n (scale n b.1 a.2) (times n (cut n a) b.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change a.1*b.2.1+a.2.1*b.1=b.1*a.2.1+a.1*b.2.1; grobner
    · change plus n (scale n a.1 b.2.2) (times (n+1) a.2 (cut (n+1) b)).2 =
        plus n (scale n b.1 a.2.2)
          (plus n (scale n a.1 b.2.2) (times n (cut n a.2) (cut n b.2)))
      rw [ih]
      exact exchange ..

theorem times_comm (n) (a b : J R n) : times n a b=times n b a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change a.1*b.1=b.1*a.1; grobner
    · rw [right_tail n a b,ih]; rfl

def con : (n : Nat) → R → J R n
  | 0, _ => ()
  | n+1, c => (c, con n 0)

theorem coeff_con (n) (a : R) (i) (h : i<n) :
    coeff n (con n a) i=if i=0 then a else 0 := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i => simpa using ih (0:R) i (by omega)

theorem plus_zero (n) (a : J R n) : plus n a (con n 0)=a := by
  apply ext_coeff n; intro i hi
  rw [coeff_plus,coeff_con _ _ _ hi]; simp; grobner

theorem zero_times (n) (a : J R n) : times n (con n 0) a=con n 0 := by
  apply ext_coeff n; intro i hi
  rw [times_comm,times_leading n a (con n 0) i hi (by
    intro j hj;rw [coeff_con _ _ _ (by omega)];simp),coeff_con _ _ _ hi];simp; grobner

theorem mul_con (n) (c : R) (a : J R n) : times n (con n c) a=scale n c a := by
  cases n with
  | zero => rfl
  | succ n =>
    refine Prod.ext (by rfl) ?_
    change plus n (scale n c a.2) (times n (con n 0) (cut n a))=_
    rw [zero_times,plus_zero]; rfl

theorem scale_one (n) (a : J R n) : scale n 1 a=a := by
  apply ext_coeff n; intro i hi; rw [coeff_scale]; grobner

theorem con_plus (n) (a b : R) : con n (a+b)=plus n (con n a) (con n b) := by
  apply ext_coeff n; intro i hi
  rw [coeff_plus,coeff_con _ _ _ hi,coeff_con _ _ _ hi,coeff_con _ _ _ hi]
  split <;> grobner

theorem scale_con (n) (a b : R) : scale n a (con n b)=con n (a*b) := by
  apply ext_coeff n; intro i hi
  rw [coeff_scale,coeff_con _ _ _ hi,coeff_con _ _ _ hi]
  split <;> grobner

theorem neg_cancel (n) (a : J R n) : plus n (scale n (-1) a) a=con n 0 := by
  apply ext_coeff n; intro i hi
  rw [coeff_plus,coeff_scale,coeff_con _ _ _ hi];simp;grobner

def power (n : Nat) (a : J R n) : Nat → J R n
  | 0 => con n 1
  | k+1 => times n (power n a k) a

instance jetRing (n) : CommRing (J R n) where
  add := plus n
  mul := times n
  neg := scale n (-1)
  sub := fun a b => plus n a (scale n (-1) b)
  natCast := ⟨fun i => con n (i:R)⟩
  ofNat := fun i => ⟨con n (i:R)⟩
  intCast := ⟨fun i => con n (i:R)⟩
  nsmul := ⟨fun i => times n (con n (i:R))⟩
  zsmul := ⟨fun i => times n (con n (i:R))⟩
  npow := ⟨power n⟩
  add_zero := by intro a; change plus n a (con n ((0:Nat):R))=_;rw [Semiring.natCast_zero,plus_zero]
  add_comm := plus_comm n
  add_assoc := plus_assoc n
  mul_assoc := times_assoc n
  mul_comm := times_comm n
  mul_one := by intro a;change times n a (con n ((1:Nat):R))=_;rw [Semiring.natCast_one,times_comm,mul_con,scale_one]
  one_mul := by intro a;change times n (con n ((1:Nat):R)) a=a;rw [Semiring.natCast_one,mul_con,scale_one]
  zero_mul := by intro a;change times n (con n ((0:Nat):R)) a=con n ((0:Nat):R);rw [Semiring.natCast_zero,zero_times]
  mul_zero := by intro a;change times n a (con n ((0:Nat):R))=con n ((0:Nat):R);rw [Semiring.natCast_zero,times_comm,zero_times]
  right_distrib := times_plus_left n
  left_distrib := times_plus_right n
  pow_zero := by intro a;change con n (1:R)=con n ((1:Nat):R);rw [Semiring.natCast_one]
  pow_succ := by intros; rfl
  ofNat_succ := by intro k;change con n ((k+1:Nat):R)=plus n (con n (k:R)) (con n ((1:Nat):R));rw [Semiring.natCast_add,con_plus]
  neg_add_cancel := by intro a;change plus n (scale n (-1) a) a=con n ((0:Nat):R);rw [Semiring.natCast_zero,neg_cancel]
  sub_eq_add_neg := by intros; rfl
  neg_zsmul := by
    intro i a
    change times n (con n ((-i:Int):R)) a=scale n (-1) (times n (con n (i:R)) a)
    rw [mul_con,mul_con,scale_scale,Ring.intCast_neg];congr 1;grobner
  zsmul_natCast_eq_nsmul := by intro k a;change times n (con n ((k:Int):R)) a=times n (con n (k:R)) a;rw [Ring.intCast_natCast]
  intCast_ofNat := by intro k;change con n ((OfNat.ofNat k:Int):R)=con n (k:R);rw [Ring.intCast_ofNat,Semiring.ofNat_eq_natCast]
  intCast_neg := by intro i;change con n ((-i:Int):R)=scale n (-1) (con n (i:R));rw [scale_con,Ring.intCast_neg];congr 1;grobner

theorem plug_con (n) (u : J R n) (c : R) : plug n u (con n c)=con n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change times n (cut n u) (plug n (cut n u) (con n 0))=con n 0
    rw [ih,times_comm,zero_times]

end WitnessTransfer.FiniteJet
