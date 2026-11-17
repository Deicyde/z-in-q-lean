import QuadraticNumerator
namespace EllipticHeight
namespace QuadraticInt
open Lean.Grind
attribute [local instance] Ring.intCast Semiring.natCast

def delta : R := (3,-1)
def rho : R := (0,1)
def sq (a : R) := mul a a
def fourth (a : R) := sq (sq a)
def chart (a b c : R) := plus (sq c) (sq (mul delta (sq b)))=fourth a

private def red {k : Nat} [NeZero k] (a : R) : Fin k × Fin k := ((a.1:Fin k),(a.2:Fin k))
private def padd {k : Nat} [NeZero k] (a b : Fin k × Fin k) := (a.1+b.1,a.2+b.2)
private def pmul {k : Nat} [NeZero k] (a b : Fin k × Fin k) := (a.1*b.1+2*a.2*b.2,a.1*b.2+a.2*b.1)
private def psq {k : Nat} [NeZero k] (a : Fin k × Fin k) := pmul a a
private theorem rplus {k : Nat} [NeZero k] (a b : R) : red (k:=k) (plus a b)=padd (red a) (red b) := by
  apply Prod.ext <;> simp [red,plus,padd,Ring.intCast_add]
private theorem rmul {k : Nat} [NeZero k] (a b : R) : red (k:=k) (mul a b)=pmul (red a) (red b) := by
  apply Prod.ext <;> simp [red,mul,pmul,Ring.intCast_add,Ring.intCast_mul] <;> grobner

private theorem no_dyadic : ∀ a a' b b' c c' : Fin 4,
    (b=1 ∨ b=3) →
    padd (psq (c,c')) (psq (pmul (3,3) (psq (b,b')))) ≠ psq (psq (a,a')) := by decide +kernel

private theorem even_rho (a : R) : divides rho a ↔ 2∣a.1 := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u.2,by dsimp [mul,rho];grobner⟩
  · rintro ⟨w,h⟩
    exact ⟨(a.2,w),Prod.ext (by dsimp [rho,mul];omega) (by dsimp [rho,mul];omega)⟩

private theorem odd_pair {a b : R} (pr : coprime a b) (ha : 2∣a.1) : ¬2∣b.1 := by
  obtain ⟨u,v,h⟩:=pr
  obtain ⟨p,hp⟩:=ha
  rintro ⟨q,hq⟩
  have e:=congrArg Prod.fst h
  change a.1*u.1+2*a.2*u.2+(b.1*v.1+2*b.2*v.2)=1 at e
  have d : (2:Int)∣1 := ⟨p*u.1+a.2*u.2+q*v.1+b.2*v.2,by rw [←e,hp,hq];grobner⟩
  exact (by decide : ¬(2:Int)∣1) d

private theorem mod_four (a : Int) :
    (2∣a → (a:Fin 4)=0 ∨ (a:Fin 4)=2) ∧ (¬2∣a → (a:Fin 4)=1 ∨ (a:Fin 4)=3) := by
  have redA (k:Int) : (a:Fin 4)=(k:Fin 4) ↔ a%4=k%4 :=
    IsCharP.intCast_ext_iff (α:=Fin 4) 4
  have a0:=redA 0
  have a1:=redA 1
  have a2:=redA 2
  have a3:=redA 3
  change ((a:Fin 4)=0 ↔ a%4=0) at a0
  change ((a:Fin 4)=1 ↔ a%4=1) at a1
  change ((a:Fin 4)=2 ↔ a%4=2) at a2
  change ((a:Fin 4)=3 ↔ a%4=3) at a3
  rw [a0,a1,a2,a3,Int.dvd_iff_emod_eq_zero]
  omega

/-- Every integral root parameter is impossible at the dyadic place.
The normalized denominator contains the dyadic prime for every signed chart. -/
theorem dyadic_denominator {a b c : R} (h : chart a b c) : divides rho b := by
  apply (even_rho b).mpr
  apply Classical.byContradiction
  intro odd
  have eq:=congrArg (red (k:=4)) h
  unfold fourth sq at eq
  simp only [rplus,rmul] at eq
  exact no_dyadic _ _ _ _ _ _ ((mod_four _).2 odd) eq

theorem no_dyadic_numerator {a b c : R} (pr : coprime a b) (h : chart a b c) :
    ¬ divides rho a := by
  intro div
  exact odd_pair pr ((even_rho a).mp div) ((even_rho b).mp (dyadic_denominator h))

private def atSeven (a : R) : Fin 7 := ((a.1+3*a.2:Int):Fin 7)
private theorem seven_plus (a b : R) : atSeven (plus a b)=atSeven a+atSeven b := by
  dsimp [atSeven,plus]
  simp only [Ring.intCast_add,Ring.intCast_mul]
  grobner
private theorem seven_mul (a b : R) : atSeven (mul a b)=atSeven a*atSeven b := by
  dsimp [atSeven,mul]
  simp only [Ring.intCast_add,Ring.intCast_mul]
  grobner

theorem delta_divides (a : R) : divides delta a ↔ atSeven a=0 := by
  constructor
  · rintro ⟨t,rfl⟩
    rw [seven_mul,show atSeven delta=0 by decide]
    exact Semiring.zero_mul _
  · intro h
    have em:=(IsCharP.intCast_eq_zero_iff (α:=Fin 7) 7 (a.1+3*a.2)).mp h
    obtain ⟨q,e⟩:=Int.dvd_iff_emod_eq_zero.mpr em
    exact ⟨(3*q-a.2,q),Prod.ext (by dsimp [delta,mul];omega) (by dsimp [delta,mul];omega)⟩

private theorem cancel_delta_square (a b c : R) :
    chart (mul delta a) b (mul delta c) →
    plus (sq c) (fourth b)=mul (sq delta) (fourth a) := by
  intro h
  have e:=congrArg Prod.fst h
  have f:=congrArg Prod.snd h
  apply Prod.ext <;> dsimp [chart,delta,plus,mul,fourth,sq] at e f ⊢ <;> grobner

theorem no_seven_numerator {a b c : R} (pr : coprime a b) (h : chart a b c) :
    ¬ divides delta a := by
  intro div
  have za:=(delta_divides a).mp div
  have zb : atSeven b ≠ 0 := by
    obtain ⟨u,v,e⟩:=pr
    have e':=congrArg atSeven e
    intro dead
    rw [seven_plus,seven_mul,seven_mul,za,dead] at e'
    exact (by decide : (0:Fin 7)*0+0*0≠atSeven (1,0)) (by simpa only [Semiring.zero_mul,AddCommMonoid.zero_add] using e')
  have v:=congrArg atSeven h
  unfold fourth sq at v
  simp only [seven_plus,seven_mul,za,show atSeven delta=0 by decide] at v
  have nil : ∀ t : Fin 7, t*t=0 → t=0 := by decide
  have zc:=nil (atSeven c) (by simpa only [Semiring.zero_mul,Semiring.add_zero] using v)
  obtain ⟨u,rfl⟩:=div
  obtain ⟨w,rfl⟩:=(delta_divides c).mpr zc
  have wv:=congrArg atSeven (cancel_delta_square u b w h)
  unfold fourth sq at wv
  simp only [seven_plus,seven_mul,show atSeven delta=0 by decide] at wv
  have anis : ∀ s t : Fin 7, s*s+(t*t)*(t*t)=0 → t=0 := by decide
  exact zb (anis (atSeven w) (atSeven b) (by simpa only [Semiring.zero_mul] using wv))

end QuadraticInt
end EllipticHeight
#print axioms EllipticHeight.QuadraticInt.dyadic_denominator
#print axioms EllipticHeight.QuadraticInt.no_dyadic_numerator
#print axioms EllipticHeight.QuadraticInt.delta_divides
#print axioms EllipticHeight.QuadraticInt.no_seven_numerator
