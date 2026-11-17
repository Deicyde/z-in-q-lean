import RootOrdinate
namespace PhysicalProjection.RootOrdinate
open PhysicalProjection.Comparison

/-- Division by `3-√2` uses rational constants only. -/
def divDelta (a : Q2) := times (3/7,1/7) a

def deltaTarget (a : Q2) := sub (sq (divDelta (sq a))) one

theorem delta_inverses (a : Q2) : times delta (divDelta a)=a ∧ divDelta (times delta a)=a := by
  constructor <;> apply Prod.ext <;> dsimp [times,divDelta,delta] <;> grobner

theorem delta_root (a b : Q2) : root a b ↔ sq (divDelta b)=deltaTarget a := by
  constructor <;> intro h <;> have x:=congrArg Prod.fst h <;> have y:=congrArg Prod.snd h
  · apply Prod.ext <;> dsimp [sq,divDelta,deltaTarget,sub,root,fourth,D2,one,times] at x y ⊢ <;> grobner
  · apply Prod.ext <;> dsimp [sq,divDelta,deltaTarget,sub,root,fourth,D2,one,times] at x y ⊢ <;> grobner

theorem delta_scalar_nonzero {a : Q2} {u : Rat} (h : equation (deltaTarget a) u=0) : a≠(0,0) := by
  intro zero;subst a
  have v : 2+2*u^2=0 := by dsimp [equation,deltaTarget,divDelta,sub,sq,times,one] at h;grobner
  have n : 0≤u^2 := by
    rcases Rat.nonneg_total u with pos|neg
    · exact Rat.pow_nonneg pos
    · have s:=Rat.mul_nonneg neg neg; rwa [show (-u)*(-u)=u^2 by grobner] at s
  grind

private theorem theta_square (a : Q2) : sq (divDelta (sq a))=times D2 (fourth (divDelta a)) := by
  have same : times delta (sq (divDelta a))=divDelta (sq a) := by
    apply Prod.ext <;> dsimp [times,delta,sq,divDelta] <;> grobner
  rw [show fourth (divDelta a)=sq (sq (divDelta a)) from rfl,delta_square,same]

theorem delta_real_nonzero {a b : Q2} (rt : root a b) : (divDelta b).1≠0 := by
  have nz:=root_nonzero rt
  have n : divDelta a≠(0,0) := by
    intro z;apply nz;rw [←(delta_inverses a).1,z];apply Prod.ext <;> dsimp [times,delta] <;> grobner
  have impossible:=fourth_imaginary_nonzero n
  have h := congrArg Prod.snd ((delta_root a b).mp rt)
  change (divDelta b).1*(divDelta b).2+(divDelta b).2*(divDelta b).1=(sq (divDelta (sq a))).2-0 at h
  rw [theta_square] at h
  intro z;rw [z] at h
  exact impossible (by change (times D2 (fourth (divDelta a))).2=0;grobner)

/-- The original signed ordinate is `δ` times the recovered pair of coefficients. -/
theorem delta_pointwise (a b : Q2) (u : Rat) :
    (root a b ∧ u*(divDelta b).1=1) ↔ equation (deltaTarget a) u=0 ∧ b=times delta (ordinate (deltaTarget a) u) := by
  constructor
  · rintro ⟨rt,unit⟩
    obtain ⟨eqn,which⟩ := (ordinate_iff (deltaTarget a) (divDelta b) u).mp ⟨(delta_root a b).mp rt,unit⟩
    exact ⟨eqn,by rw [←which,(delta_inverses b).1]⟩
  · rintro ⟨eqn,rfl⟩
    have both:=ordinate_from_equation (deltaTarget a) u eqn
    have back:=(delta_inverses (ordinate (deltaTarget a) u)).2
    exact ⟨(delta_root ..).mpr (by rw [back];exact both.1),by rw [back];exact both.2⟩

theorem delta_equivalence (a : Q2) : (∃ b : Q2,root a b) ↔ ∃ u : Rat,equation (deltaTarget a) u=0 := by
  constructor
  · rintro ⟨b,rt⟩
    exact ⟨(divDelta b).1⁻¹,((delta_pointwise ..).mp ⟨rt,Rat.inv_mul_cancel _ (delta_real_nonzero rt)⟩).1⟩
  · rintro ⟨u,eqn⟩; exact ⟨_,((delta_pointwise a _ u).mpr ⟨eqn,rfl⟩).1⟩

/-- Four root and four comparison ordinates reconstructed without any variable denominator. -/
theorem eight_points_delta (a b r J : Fin 4→Q2) :
    (∀ i, root (a i) (b i) ∧ conic (r i) (J i)) ↔ ∃ u v : Fin 4→Rat, ∀ i,
      (equation (deltaTarget (a i)) (u i)=0 ∧ b i=times delta (ordinate (deltaTarget (a i)) (u i))) ∧
      (equation (target (r i)) (v i)=0 ∧ J i=ordinate (target (r i)) (v i)) := by
  constructor
  · intro h;refine ⟨fun i=>(divDelta (b i)).1⁻¹,fun i=>(J i).1⁻¹,?_⟩;intro i
    exact ⟨(delta_pointwise ..).mp ⟨(h i).1,Rat.inv_mul_cancel _ (delta_real_nonzero (h i).1)⟩,
           (comparison_pointwise ..).mp ⟨(h i).2,Rat.inv_mul_cancel _ (ordinate_real_nonzero (h i).2)⟩⟩
  · rintro ⟨u,v,h⟩ i
    exact ⟨((delta_pointwise (a i) (b i) (u i)).mpr (h i).1).1,
           ((comparison_pointwise (r i) (J i) (v i)).mpr (h i).2).1⟩

#print axioms delta_inverses
#print axioms delta_root
#print axioms delta_scalar_nonzero
#print axioms delta_real_nonzero
#print axioms delta_pointwise
#print axioms delta_equivalence
#print axioms eight_points_delta
end PhysicalProjection.RootOrdinate
