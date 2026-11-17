import PrescribedNorm
import ScalarInput

namespace Sun28.PointFibres
open Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses Sun28.PreparedPoles
  Sun28.TwistExtension Sun28.TwistRank Sun28.ScalarHeight Sun28.FixedPreparation
  Sun28.ContactFactors ZInQ.RouteK
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def first : ℕ := 526361
def second : ℕ := 526681
def u : ℚ := -31116809484180676952006920957273956468097068208800/2717103063107875996162129575261807982370252712444944671
def v : ℚ := 3743840131329986488718957228053091018889923581528819/2717103063107875996162129575261807982370252712444944671
def pole : ℚ := 15*first*u^2

private theorem norm_equation : (first:ℚ)*u^2+second*v^2=1 := by norm_num [first,second,u,v]

private theorem symbol_from_root {p d : ℕ} (hp:p.Prime) (odd:p≠2)
    (unit:(d:ZMod p)≠0) (root:∃ x:ZMod p,(d:ZMod p)=x^2) : LocalSquareAt p d := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply local_square_of_legendre odd
  apply (legendreSym.eq_one_iff' p unit).mpr
  obtain ⟨x,h⟩:=root
  exact ⟨x,by simpa [pow_two] using h⟩

private theorem base_square {p:ℕ} (pp:p.Prime) (div:p∣first) : LocalSquareAt p second := by
  change p∣526361 at div
  rw [show (526361:ℕ)=11*(109*439) by decide] at div
  rcases pp.dvd_mul.mp div with hit|d
  · have e:= (Nat.prime_dvd_prime_iff_eq pp (show Nat.Prime 11 by decide)).mp hit
    subst p;exact symbol_from_root (by decide) (by decide) (by decide) ⟨1,by decide⟩
  · rcases pp.dvd_mul.mp d with hit|hit
    · have e:=(Nat.prime_dvd_prime_iff_eq pp (show Nat.Prime 109 by norm_num)).mp hit
      subst p;exact symbol_from_root (by norm_num) (by decide) (by decide) ⟨50,by decide⟩
    · have e:=(Nat.prime_dvd_prime_iff_eq pp (show Nat.Prime 439 by norm_num)).mp hit
      subst p;exact symbol_from_root (by norm_num) (by decide) (by decide) ⟨205,by decide⟩

theorem prescribed_classes : PreparedClasses pole 15 first second := by
  have prime : Nat.Prime second:=by norm_num [second]
  have sf : Squarefree first:=scalar_zero_input.2
  have un : u≠0:=by norm_num [u]
  have vn : v≠0:=by norm_num [v]
  have pn : pole≠0:=by norm_num [pole,first,u]
  refine ⟨by decide,by decide,sf,prime.squarefree,by decide,by decide,by decide,by decide,
    by decide,?_,fun _ => base_square,⟨15*u,mul_ne_zero (by norm_num) un,by unfold pole;ring⟩,?_⟩
  · intro p pp d;have ep:=(Nat.prime_dvd_prime_iff_eq pp prime).mp d;subst p
    exact symbol_from_root prime (by decide) (by decide) ⟨125467,by decide⟩
  · refine ⟨15*pole*v,mul_ne_zero (mul_ne_zero (by norm_num) pn) vn,?_⟩
    change 15*pole*(15*pole-pole^2)=(second:ℚ)*(15*pole*v)^2
    have h:=norm_equation
    dsimp [pole]
    linear_combination -50625*(first:ℚ)^2*u^4*h

private theorem high_order {p:ℕ} [Fact p.Prime] {q:ℚ} (qn:q≠0)
    (div : (p:ℤ)^4∣q.num) (den:¬p∣q.den) : 4≤padicValRat p q := by
  have pos : 4≤padicValInt p q.num:=(padicValInt_dvd_iff 4 q.num).mp div |>.resolve_left
    (Rat.num_ne_zero.mpr qn)
  rw [padicValRat_def,padicValNat.eq_zero_of_not_dvd den]
  simp only [Nat.cast_zero,sub_zero]
  exact_mod_cast pos

private theorem pole_fraction : pole.num=7644781623558995619988317199157035367226075835164206282644651596628131714962353086003790054188553737600000 ∧ pole.den=7382649055550202368204234257641466786483262283028891932027791098553409367903051221905166730453371264251298241 := by
  have val : pole=mkRat 7644781623558995619988317199157035367226075835164206282644651596628131714962353086003790054188553737600000 7382649055550202368204234257641466786483262283028891932027791098553409367903051221905166730453371264251298241 := by
    rw [←Rat.divInt_ofNat, Rat.divInt_eq_div];norm_num [pole,first,u]
  rw [val,Rat.num_mkRat,Rat.den_mkRat];decide

theorem pole_prepared : Prepared pole := by
  refine ⟨⟨2717103063107875996162129575261807982370252712444944671,by rw [pole_fraction.2]⟩,by norm_num [pole,first,u],by norm_num [pole,first,u],?_⟩
  intro p hp
  have pp : p.Prime:= (show ∀ j∈primes,Nat.Prime j by decide) p hp
  let _ : Fact p.Prime:=⟨pp⟩
  apply high_order (by norm_num [pole,first,u])
  · rw [pole_fraction.1];exact (show ∀ j∈primes,(j:ℤ)^4∣7644781623558995619988317199157035367226075835164206282644651596628131714962353086003790054188553737600000 by decide) p hp
  · rw [pole_fraction.2];exact (show ∀ j∈primes,¬j∣7382649055550202368204234257641466786483262283028891932027791098553409367903051221905166730453371264251298241 by decide) p hp

def traceInput : ℚ := u*(1+(denominator:ℚ)*31581660^2)/(2*(gamma:ℚ))

/-- Normalization at the actual scalar X=0, with W specified as a rational value. -/
theorem scalar_input_value : traceInput≠0 ∧
    signedValue (scalarRadicand (beta (0:ℚ))) (-1) gamma denominator traceInput=pole := by
  norm_num [traceInput,u,denominator,gamma,FixedPreparation.primorial,signedValue,scalarRadicand,beta,pole,first]

theorem scalar_input_prepared : ClassPrepared pole := by
  refine ⟨pole_prepared,?_⟩
  intro m β θ mem h
  have H:=h
  rw [←scalar_input_value.2] at H
  have pos : 0<signedValue (scalarRadicand (beta ((0:ℤ):ℚ))) (-1) gamma denominator traceInput:=by
    simpa only [Int.cast_zero,scalar_input_value.2] using pole_prepared.2.1
  have eqn : (-1:ℚ)*scalarRadicand (beta ((0:ℤ):ℚ))=((integerRadicand 0).natAbs:ℚ):=by
    norm_num [scalarRadicand,beta,integerRadicand]
  exact Or.inr ⟨0,m,(scalar_class (X:=0) H pos eqn).1,mem,(scalar_class (X:=0) H pos eqn).2⟩

theorem fixed_conditions : AdmissiblePair first second ∧ InputClass first ∧ FixedSquares second ∧
    NormConic first second ∧ (15:ℚ)∈smallMultipliers := by
  have h:=prescribed_classes
  have mem:(15:ℚ)∈smallMultipliers:=by decide
  have ⟨loc,norm⟩:=actual_pair pole_prepared (m:=15) mem h
  exact ⟨⟨h.beta_positive,h.theta_positive,h.beta_sf,h.theta_sf,h.disjoint,h.beta_six,h.theta_six,
    h.beta_mod,h.theta_mod,h.beta_local,h.theta_local⟩,scalar_zero_input.1,loc,norm,mem⟩

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.prescribed_classes
#print axioms Sun28.PointFibres.pole_prepared
#print axioms Sun28.PointFibres.scalar_input_value
#print axioms Sun28.PointFibres.scalar_input_prepared
#print axioms Sun28.PointFibres.fixed_conditions
