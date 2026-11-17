import Std

namespace WitnessTransfer.FiniteJet
open Lean.Grind

/-- The coefficients of degrees strictly below n, in increasing order. -/
def J (R : Type) : Nat → Type
  | 0 => Unit
  | n+1 => R × J R n

variable {R : Type} [CommRing R]

def cut : (n : Nat) → J R (n+1) → J R n
  | 0, _ => ()
  | n+1, a => (a.1, cut n a.2)

def plus : (n : Nat) → J R n → J R n → J R n
  | 0, _, _ => ()
  | n+1, a, b => (a.1+b.1, plus n a.2 b.2)

def scale : (n : Nat) → R → J R n → J R n
  | 0, _, _ => ()
  | n+1, c, a => (c*a.1, scale n c a.2)

def times : (n : Nat) → J R n → J R n → J R n
  | 0, _, _ => ()
  | n+1, a, b => (a.1*b.1, plus n (scale n a.1 b.2) (times n a.2 (cut n b)))

/-- Substitution f(X u(X)) with all coefficients truncated to the same precision. -/
def plug : (n : Nat) → J R n → J R n → J R n
  | 0, _, _ => ()
  | n+1, u, f => (f.1, times n (cut n u) (plug n (cut n u) f.2))

theorem plus_assoc (n) (a b c : J R n) :
    plus n (plus n a b) c = plus n a (plus n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [plus]
    congr 1
    · grobner
    · apply ih

theorem plus_comm (n) (a b : J R n) : plus n a b=plus n b a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [plus]
    congr 1
    · grobner
    · apply ih

private theorem middle (n) (a b c d : J R n) :
    plus n (plus n a b) (plus n c d) = plus n (plus n a c) (plus n b d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [plus]
    congr 1
    · grobner
    · apply ih

theorem scale_plus (n) (k : R) (a b : J R n) :
    scale n k (plus n a b)=plus n (scale n k a) (scale n k b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [scale,plus]
    congr 1
    · grobner
    · apply ih

theorem plus_scale (n) (k h : R) (a : J R n) :
    scale n (k+h) a=plus n (scale n k a) (scale n h a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [scale,plus]
    congr 1
    · grobner
    · apply ih

theorem scale_scale (n) (k h : R) (a : J R n) :
    scale n k (scale n h a)=scale n (k*h) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [scale]
    congr 1
    · grobner
    · apply ih

theorem cut_plus (n) (a b : J R (n+1)) :
    cut n (plus (n+1) a b)=plus n (cut n a) (cut n b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih a.2 b.2)

theorem cut_scale (n) (c : R) (a : J R (n+1)) :
    cut n (scale (n+1) c a)=scale n c (cut n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih a.2)

theorem cut_times (n) (a b : J R (n+1)) :
    cut n (times (n+1) a b)=times n (cut n a) (cut n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change cut n (plus (n+1) (scale (n+1) a.1 b.2) (times (n+1) a.2 (cut (n+1) b)))=_
    rw [cut_plus,cut_scale,ih]
    rfl

theorem times_plus_left (n) (a b c : J R n) :
    times n (plus n a b) c=plus n (times n a c) (times n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [times,plus,plus_scale,ih]
    apply Prod.ext
    · grobner
    · apply middle (R:=R)

theorem times_plus_right (n) (a b c : J R n) :
    times n a (plus n b c)=plus n (times n a b) (times n a c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change a.1*(b.1+c.1)=a.1*b.1+a.1*c.1; grobner
    · change plus n (scale n a.1 (plus n b.2 c.2)) (times n a.2 (cut n (plus (n+1) b c)))=_
      rw [cut_plus,scale_plus,ih]
      apply middle (R:=R)

theorem times_scale_left (n) (c : R) (a b : J R n) :
    times n (scale n c a) b=scale n c (times n a b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [times,scale,scale_plus,ih,scale_scale]
    apply Prod.ext
    · grobner
    · rfl

theorem times_scale_right (n) (c : R) (a b : J R n) :
    times n a (scale n c b)=scale n c (times n a b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change a.1*(c*b.1)=c*(a.1*b.1); grobner
    · change plus n (scale n a.1 (scale n c b.2)) (times n a.2 (cut n (scale (n+1) c b))) =
        scale n c (plus n (scale n a.1 b.2) (times n a.2 (cut n b)))
      rw [cut_scale,ih,scale_plus,scale_scale,scale_scale,CommSemiring.mul_comm a.1 c]

theorem times_assoc (n) (a b c : J R n) :
    times n (times n a b) c=times n a (times n b c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (a.1*b.1)*c.1=a.1*(b.1*c.1); grobner
    · change plus n (scale n (a.1*b.1) c.2)
        (times n (plus n (scale n a.1 b.2) (times n a.2 (cut n b))) (cut n c)) =
        plus n (scale n a.1 (plus n (scale n b.1 c.2) (times n b.2 (cut n c))))
        (times n a.2 (cut n (times (n+1) b c)))
      rw [cut_times,times_plus_left,times_scale_left,ih,scale_plus,scale_scale,plus_assoc]

theorem cut_plug (n) (u f : J R (n+1)) :
    cut n (plug (n+1) u f)=plug n (cut n u) (cut n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change cut n (times (n+1) (cut (n+1) u) (plug (n+1) (cut (n+1) u) f.2))=_
    rw [cut_times,ih]
    rfl

theorem plug_plus (n) (u f g : J R n) :
    plug n u (plus n f g)=plus n (plug n u f) (plug n u g) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [plug,plus,ih,times_plus_right]

theorem plug_scale (n) (k : R) (u f : J R n) :
    plug n u (scale n k f)=scale n k (plug n u f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [plug,scale,ih,times_scale_right]

theorem plug_times (n) (u f g : J R n) :
    plug n u (times n f g)=times n (plug n u f) (plug n u g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change times n (cut n u)
        (plug n (cut n u) (plus n (scale n f.1 g.2) (times n f.2 (cut n g)))) =
        plus n (scale n f.1 (times n (cut n u) (plug n (cut n u) g.2)))
        (times n (times n (cut n u) (plug n (cut n u) f.2)) (cut n (plug (n+1) u g)))
    rw [cut_plug,plug_plus,plug_scale,ih,times_plus_right,times_scale_right,times_assoc]

/-- Algebraic composition on the actual truncated coefficient lists. -/
theorem double_substitution (n) (v u f : J R n) :
    plug n v (plug n u f)=plug n (times n v (plug n v u)) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Prod.ext (by rfl) ?_
    change times n (cut n v) (plug n (cut n v) (times n (cut n u) (plug n (cut n u) f.2))) =
        times n (cut n (times (n+1) v (plug (n+1) v u)))
          (plug n (cut n (times (n+1) v (plug (n+1) v u))) f.2)
    rw [cut_times,cut_plug,plug_times,ih,times_assoc]

end WitnessTransfer.FiniteJet
