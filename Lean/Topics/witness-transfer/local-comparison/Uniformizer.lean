import JetRing

namespace WitnessTransfer.FiniteJet
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {R : Type} [CommRing R]

def X : (n : Nat) → J R n
  | 0 => ()
  | n+1 => (0, con n 1)

theorem con_zero (n) : con n (0:R)=0 := by change con n 0=con n ((0:Nat):R);rw [Semiring.natCast_zero]
theorem con_one (n) : con n (1:R)=1 := by change con n 1=con n ((1:Nat):R);rw [Semiring.natCast_one]

theorem cut_con (n) (c : R) : cut n (con (n+1) c)=con n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih 0)

theorem cut_X (n) : cut n (X (R:=R) (n+1))=X n := by
  cases n with
  | zero => rfl
  | succ n => exact Prod.ext rfl (cut_con n 1)

theorem X_mul (n) (f : J R (n+1)) : X (n+1)*f=(0,cut n f) := by
  apply Prod.ext
  · change (0:R)*f.1=0;grobner
  · change plus n (scale n 0 f.2) (times n (con n 1) (cut n f))=_
    rw [← mul_con,zero_times,mul_con,scale_one,plus_comm,plus_zero]

theorem cut_pow (n) (f : J R (n+1)) (i : Nat) : cut (R:=R) n (f^i)=(cut n f)^i := by
  induction i with
  | zero => rw [Semiring.pow_zero,Semiring.pow_zero,← con_one n,← con_one (n+1),cut_con]
  | succ i ih =>
    rw [Semiring.pow_succ,Semiring.pow_succ]
    exact (cut_times n _ _).trans (congrArg (fun a => times n a (cut n f)) ih)

theorem X_nil (n) : (X n : J R n)^n=0 := by
  induction n with
  | zero => exact @Subsingleton.elim Unit inferInstance _ _
  | succ n ih =>
    rw [Semiring.pow_succ,CommSemiring.mul_comm,X_mul,cut_pow,cut_X,ih,← con_zero]
    rw [← con_zero (R:=R) (n+1)];rfl

theorem plug_X (n) (u : J R n) : plug n u (X n)=X n*u := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [X_mul];refine Prod.ext (by rfl) ?_
    change times n (cut n u) (plug n (cut n u) (con n 1))=cut n u
    rw [plug_con,times_comm,mul_con,scale_one]

/-- Literal equality of the two compositions on X in the SAME truncated ring. -/
theorem commutes_iff (n) (m d : J R n) : commutes n m d ↔
    plug n d (X n*m)=plug n m (X n*d) := by
  change _ ↔ plug n d (times n (X n) m)=plug n m (times n (X n) d)
  rw [plug_times,plug_times,plug_X,plug_X]
  change _ ↔ (X n*d)*plug n d m=(X n*m)*plug n m d
  rw [Semiring.mul_assoc,Semiring.mul_assoc]
  cases n with
  | zero => exact ⟨fun _=>rfl,fun _=>trivial⟩
  | succ n =>
    rw [X_mul,X_mul]
    exact ⟨fun h=>Prod.ext rfl h,fun h=>congrArg Prod.snd h⟩

theorem plug_int (n) (u : J R n) (i : Int) : plug n u (i:J R n)=i :=
  plug_con n u (i:R)

theorem plug_poly (n) (u f : J R n) (a : List Int) :
    plug n u (a.foldr (fun (i : Int) t => (i:J R n)+f*t) 0) =
    a.foldr (fun (i : Int) t => (i:J R n)+(plug n u f)*t) 0 := by
  induction a with
  | nil => change plug n u 0=0; rw [← con_zero (R:=R) n,plug_con]
  | cons i a ih =>
    change plug n u (plus n (i:J R n) (times n f _))=_
    rw [plug_plus,plug_int,plug_times,ih];rfl

/-- A truncated series with invertible constant has an explicit inverse, working
coefficient by coefficient. -/
theorem unit_from_constant (n) (f : J R n)
    (good : 0<n → ∃ c : R,c*coeff n f 0=1) : ∃ b : J R n,b*f=1 := by
  induction n with
  | zero => exact ⟨(),@Subsingleton.elim Unit inferInstance _ _⟩
  | succ n ih =>
    obtain ⟨b,hb⟩:=good (by omega)
    obtain ⟨c,hc⟩:=ih (cut n f) (by intro hn;rw [coeff_cut n f 0 hn];exact ⟨b,hb⟩)
    refine ⟨(b,-(scale n b f.2)*c), Prod.ext ?_ ?_⟩
    · change b*f.1=((1:Nat):R);rw [Semiring.natCast_one];exact hb
    · change scale n b f.2 + (-(scale n b f.2)*c)*(cut n f) = con n 0
      rw [Semiring.mul_assoc,hc,con_zero]
      grobner

theorem unit_of_head {K : Type} [Field K] (n) (f : J K n)
    (good : 0<n → coeff n f 0≠0) : ∃ b : J K n,b*f=1 :=
  unit_from_constant n f (fun hn => ⟨(coeff n f 0)⁻¹,Field.inv_mul_cancel (good hn)⟩)

end WitnessTransfer.FiniteJet
