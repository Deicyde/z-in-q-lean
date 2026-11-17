import GuardedTower
import PoleParameters
import ScalarMultipliers

/-! Two monic square equations for the pole test with rational argument b/d. -/
open Polynomial ZInQBlueprint.SunResultant Sun28.RootCharts
namespace Sun28.Concrete
open Sun28.Ordinary Sun28.Forward
noncomputable section
variable {R : Type*} [CommRing R] {n : ℕ}

def Row.tested (r : Row R n) (E G : List (Test R n)) : Row R n :=
  ⟨r.tower,r.equations++E,r.guards++G⟩

theorem tested_iff (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (E G : List (Test R n)) :
    (r.tested E G).Holds φ x ↔ r.Holds φ x ∧ (∀ f∈E,ev φ x f=0) ∧ ∀ g∈G,ev φ x g≠0 := by
  simp only [Row.tested,Row.Holds,List.forall_mem_append]
  tauto

def Row.square (r : Row R n) (q : Test R n) : Row R (n+1) :=
  ⟨r.tower.adjoin (X^2-C q) (monic_X_pow_sub_C _ (by decide)),r.equations.map liftTest,r.guards.map liftTest⟩

theorem square_iff (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (q : Test R n) (w : ℚ) :
    (r.square q).Holds φ (Fin.cons w x) ↔ r.Holds φ x ∧ w^2=ev φ x q := by
  simp only [Row.square,Row.Holds,ParamTower.Satisfies,Fin.tail_cons,Fin.cons_zero,
    List.forall_mem_map,eval_lift,IsRoot.def,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,
    Polynomial.map_C,eval_sub,eval_pow,eval_X,eval_C,sub_eq_zero]
  tauto

structure PoleData (R : Type*) where
  num : R
  den : R
  e : R
  z : R

def PoleData.a (p : PoleData R) (m : ℤ) := (m:R)*p.num
def PoleData.h (p : PoleData R) (m : ℤ) := p.a m*(p.a m*p.den-p.num^2)
def PoleData.nz (p : PoleData R) (m : ℤ) := p.a m*p.e*p.h m*p.z
def PoleData.first (p : PoleData R) (m : ℤ) :=
  let a := p.a m
  p.den*a*(a-p.den*p.e)*(a+3*p.den*p.e)
def PoleData.second (p : PoleData R) (m : ℤ) :=
  let a := p.a m
  let h := p.h m
  let t := a*p.z^2*p.den^2
  p.den*a*(t-p.e*h)*(t+3*p.e*h)

theorem clear_pole (p : PoleData R) (f : R →+* ℚ) (m : ℤ) (hd : f p.den≠0) :
    poleBranch (m:ℚ) (f p.num/f p.den) (f p.e) (f p.z) ↔
      f (p.nz m) ≠ 0 ∧ ∃ w₁ w₂ : ℚ, w₁^2=f (p.first m) ∧ w₂^2=f (p.second m) := by
  let d := f p.den
  let a := (m:ℚ)*(f p.num/d)
  let h := a*(a-(f p.num/d)^2)
  have eqA : f (p.a m)=d*a := by simp [PoleData.a,a,d]; field_simp
  have eqH : f (p.h m)=d^3*h := by
    simp only [PoleData.h,map_mul,map_sub,map_pow,eqA]
    dsimp [h,a,d]; field_simp
  have nz : f (p.nz m)=d^4*(a*f p.e*h*f p.z) := by
    simp only [PoleData.nz,map_mul,eqA,eqH]; ring
  have eq₁ : f (p.first m)=d^4*(a*(a-f p.e)*(a+3*f p.e)) := by
    simp [PoleData.first,eqA,d,map_ofNat]; ring
  have eq₂ : f (p.second m)=d^8*(a*(a*(f p.z)^2-f p.e*h)*(a*(f p.z)^2+3*f p.e*h)) := by
    simp [PoleData.second,eqA,eqH,d,map_ofNat]; ring
  change (a*f p.e*h*f p.z≠0 ∧ ∃ y u : ℚ, y^2=a*(a-f p.e)*(a+3*f p.e) ∧
    u^2=a*(a*(f p.z)^2-f p.e*h)*(a*(f p.z)^2+3*f p.e*h)) ↔ _
  rw [nz,eq₁,eq₂]
  have dn : d≠0 := hd
  constructor
  · rintro ⟨hg,y,u,hy,hu⟩
    refine ⟨mul_ne_zero (pow_ne_zero _ dn) hg,d^2*y,d^4*u,?_,?_⟩
    · rw [mul_pow,hy]; ring
    · rw [mul_pow,hu]; ring
  · rintro ⟨hg,w,t,hw,ht⟩
    refine ⟨(mul_ne_zero_iff.mp hg).2,w/d^2,t/d^4,?_,?_⟩
    · rw [div_pow,hw]; field_simp
    · rw [div_pow,ht]; field_simp

def zeroPole (r : Row R n) (p : PoleData (Test R n)) := r.tested [p.num] [p.den]

def nonzeroPole (r : Row R n) (p : PoleData (Test R n)) (m : ℤ) : Row R (n+2) :=
  (((r.tested [] [p.den,p.nz m]).square (p.first m)).square (liftTest (p.second m)))

theorem zero_pole_iff (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (p : PoleData (Test R n)) :
    (zeroPole r p).Holds φ x ↔ r.Holds φ x ∧ ev φ x p.den≠0 ∧ ev φ x p.num / ev φ x p.den=0 := by
  rw [zeroPole,tested_iff]; simp [div_eq_zero_iff]; tauto

theorem nonzero_pole_iff (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (p : PoleData (Test R n)) (m : ℤ) :
    (∃ w t : ℚ, (nonzeroPole r p m).Holds φ (Fin.cons t (Fin.cons w x))) ↔
      r.Holds φ x ∧ ev φ x p.den≠0 ∧
        poleBranch (m:ℚ) (ev φ x p.num/ev φ x p.den) (ev φ x p.e) (ev φ x p.z) := by
  have tests : (r.tested [] [p.den,p.nz m]).Holds φ x ↔
      r.Holds φ x ∧ ev φ x p.den≠0 ∧ ev φ x (p.nz m)≠0 := by
    rw [tested_iff]
    simp
  simp only [nonzeroPole,square_iff,eval_lift,tests]
  constructor
  · rintro ⟨w,t,⟨⟨hr,hd,hg⟩,hw⟩,ht⟩
    exact ⟨hr,hd,(clear_pole p (ev φ x) m hd).2 ⟨hg,w,t,hw,ht⟩⟩
  · rintro ⟨hr,hd,hb⟩
    obtain ⟨hg,w,t,hw,ht⟩ := (clear_pole p (ev φ x) m hd).1 hb
    exact ⟨w,t,⟨⟨hr,hd,hg⟩,hw⟩,ht⟩

/-- Sun's 64 possible signed multipliers, before the rational input is chosen. -/
def poleMultipliers : List ℤ :=
  (Finset.univ : Finset (Bool × Bool × Bool × Fin 8)).toList.map
    fun ⟨sign,two,three,i⟩ => Sun28.ScalarHeight.shift sign two three i

theorem multiplier_mem (q : ℚ) :
    q ∈ Sun28.ScalarHeight.smallMultipliers ↔ ∃ j∈poleMultipliers, (j:ℚ)=q := by
  simp only [Sun28.ScalarHeight.smallMultipliers,poleMultipliers,List.mem_map,
    Finset.mem_image,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨s,t,h,i⟩,rfl⟩
    exact ⟨_,⟨⟨s,t,h,i⟩,rfl⟩,rfl⟩
  · rintro ⟨m,⟨⟨s,t,h,i⟩,rfl⟩,rfl⟩
    exact ⟨⟨s,t,h,i⟩,rfl⟩

def poleRows {m : ℕ} (r : Row (Sun28.Branches.Poly m) n) (p : PoleData (Test (Sun28.Branches.Poly m) n)) :
    List (Sun28.Compiler.Branch m) :=
  (zeroPole r p).branch :: poleMultipliers.map (fun j => (nonzeroPole r p j).branch)

/-- A zero argument adds no roots. A nonzero argument adds two, over precisely the
previous root tuple. In both cases a zero denominator rejects the row. -/
theorem pole_rows_spec {m : ℕ} (r : Row (Sun28.Branches.Poly m) n)
    (p : PoleData (Test (Sun28.Branches.Poly m) n)) (u : Fin m → ℚ) :
    (∃ b∈poleRows r p, Sun28.Compiler.Solutions b.tower b.equations b.guards u) ↔
      ∃ x, r.Holds (Sun28.Branches.value u) x ∧
        let f := ev (Sun28.Branches.value u) x
        f p.den≠0 ∧ poleAt Sun28.ScalarHeight.smallMultipliers (f p.num / f p.den) (f p.e) (f p.z) := by
  let φ := Sun28.Branches.value u
  constructor
  · rintro ⟨b,hb,hs⟩
    rcases List.mem_cons.mp hb with rfl|h
    · obtain ⟨x,hx⟩ := (row_solutions ..).1 hs
      obtain ⟨hr,hd,hz⟩ := (zero_pole_iff ..).1 hx
      exact ⟨x,hr,hd,Or.inl hz⟩
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
      obtain ⟨t,ht⟩ := (row_solutions ..).1 hs
      let x := Fin.tail (Fin.tail t)
      have h := (nonzero_pole_iff r φ x p j).1
        ⟨Fin.tail t 0,t 0,by simpa only [x,Fin.cons_self_tail] using ht⟩
      exact ⟨x,h.1,h.2.1,Or.inr ⟨_,(multiplier_mem _).2 ⟨j,hj,rfl⟩,h.2.2⟩⟩
  · rintro ⟨x,hr,hd,hz|⟨q,hq,hb⟩⟩
    · exact ⟨_,List.mem_cons_self,(row_solutions ..).2 ⟨x,(zero_pole_iff ..).2 ⟨hr,hd,hz⟩⟩⟩
    · obtain ⟨j,hj,rfl⟩ := (multiplier_mem q).1 hq
      obtain ⟨s,t,ht⟩ := (nonzero_pole_iff r φ x p j).2 ⟨hr,hd,hb⟩
      exact ⟨_,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,hj,rfl⟩),(row_solutions ..).2 ⟨_,ht⟩⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.tested_iff
#print axioms Sun28.Concrete.square_iff
#print axioms Sun28.Concrete.clear_pole
#print axioms Sun28.Concrete.zero_pole_iff
#print axioms Sun28.Concrete.nonzero_pole_iff
#print axioms Sun28.Concrete.multiplier_mem
#print axioms Sun28.Concrete.pole_rows_spec
