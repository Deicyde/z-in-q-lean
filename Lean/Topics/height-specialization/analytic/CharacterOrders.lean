import EulerProducts
namespace HeightSpecialization.Analytic
open Lean.Grind

/-- Exponent of two in a positive integer, with zero used only as a sentinel. -/
def twos (n : Nat) : Nat :=
  if h : 0<n ∧ 2∣n then twos (n/2)+1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self h.1 (by decide)

theorem dyadic_divides (n : Nat) : 2^twos n∣n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : 0<n ∧ 2∣n
    · obtain ⟨s,e⟩:=ih (n/2) (Nat.div_lt_self h.1 (by decide))
      have eq:=Nat.div_mul_cancel h.2
      rw [twos,dif_pos h,Nat.pow_succ]
      exact ⟨s,calc n=(n/2)*2 := eq.symm
                    _=(2^twos (n/2)*s)*2 := congrArg (·*2) e
                    _=_ := by ac_rfl⟩
    · rw [twos,dif_neg h];simp

/-- The dyadic local character at 2 has order at most 2. -/
def localExponent (p : Nat) := if p=2 then 1 else twos (p-1)

def extend (b : Nat) : List Nat→Nat
  | [] => b
  | p::ps => max (localExponent p) (extend b ps)

theorem base_le (b : Nat) (ps : List Nat) : b≤extend b ps := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih => exact Nat.le_trans ih (Nat.le_max_right ..)

theorem exponent_le_of_mem {p : Nat} {ps : List Nat} (b : Nat) (member : p∈ps) :
    localExponent p≤extend b ps := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons a tail ih =>
    rcases List.mem_cons.mp member with rfl|h
    · exact Nat.le_max_left .. 
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

def cap (sigma : List Nat) := 2^(extend 1 sigma)

private theorem pow_divides {a b : Nat} (le : a≤b) : 2^a∣2^b := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le le
  exact ⟨2^k,Nat.pow_add ..⟩

private theorem peak (b : Nat) (ps : List Nat) {t : Nat} (le : t≤2^extend b ps) :
    t≤2^b ∨ ∃p∈ps,t≤2^(localExponent p) := by
  induction ps with
  | nil => exact Or.inl le
  | cons q qs ih =>
    change t≤2^max (localExponent q) (extend b qs) at le
    by_cases head : extend b qs≤localExponent q
    · exact Or.inr ⟨q,by simp,by simpa only [Nat.max_eq_left head] using le⟩
    · rcases ih (by simpa only [Nat.max_eq_right (show localExponent q≤extend b qs by omega)] using le) with a|⟨p,m,h⟩
      · exact Or.inl a
      · exact Or.inr ⟨p,List.mem_cons_of_mem _ m,h⟩

def localProduct {Γ F : Type} [CommRing F] (f : Nat→Γ→F) (g : Γ) : List Nat→F
  | [] => 1
  | p::ps => f p g*localProduct f g ps

theorem pow_times {F : Type} [CommRing F] (u : F) (a b : Nat) : u^(a*b)=(u^a)^b := by
  induction b with
  | zero => simp only [Nat.mul_zero,Semiring.pow_zero]
  | succ n ih => rw [Nat.mul_succ,Semiring.pow_add,Semiring.pow_succ,ih]

private theorem raise_order {F : Type} [CommRing F] {u : F} {n l : Nat}
    (unity : u^n=1) (div : n∣l) : u^l=1 := by
  obtain ⟨k,rfl⟩:=div
  rw [pow_times,unity,Semiring.one_pow]

private theorem product_order {Γ F : Type} [CommRing F] (loc : Nat→Γ→F) (g : Γ) (ps : List Nat)
    (L : Nat) (each : ∀p∈ps, loc p g^L=1) : (localProduct loc g ps)^L=1 := by
  induction ps with
  | nil => exact Semiring.one_pow _
  | cons p ps ih =>
    rw [localProduct,CommSemiring.mul_pow,each p (by simp),Semiring.one_mul]
    exact ih (fun q h=>each q (List.mem_cons_of_mem _ h))

/-- Inputs from the squared modular determinant and the local finite Dirichlet
characters. Multiplicativity of the supplied functions is unnecessary here. -/
structure CharacterData (sigma ps : List Nat) (t : Nat) where
  Γ : Type
  F : Type
  [ring : CommRing F]
  localValue : Nat→Γ→F
  epsilon : Γ→F
  localUnity : ∀p∈sigma++ps,∀g,localValue p g^(2^localExponent p)=1
  determinant : ∀g,epsilon g^2 * (localProduct localValue g (sigma++ps))^2=1
  orderPos : 0<t
  unity : ∀g,epsilon g^t=1
  least : ∀ n,0<n → (∀g,epsilon g^n=1) → t≤n

def totalExponent (sigma ps : List Nat) := extend (extend 1 sigma) ps

theorem annihilates {sigma ps : List Nat} {t : Nat} (c : CharacterData sigma ps t) :
    letI := c.ring
    ∀g,c.epsilon g^(2^totalExponent sigma ps)=1 := by
  letI:=c.ring
  let e:=extend (extend 1 sigma) ps
  let L:=2^e
  have one : 1≤e := Nat.le_trans (base_le 1 sigma) (base_le _ ps)
  have all (p : Nat) (h : p∈sigma++ps) : localExponent p≤e := by
    rcases List.mem_append.mp h with a|a
    · exact Nat.le_trans (exponent_le_of_mem 1 a) (base_le _ ps)
    · exact exponent_le_of_mem _ a
  intro g
  change c.epsilon g^L=1
  have ch : (localProduct c.localValue g (sigma++ps))^L=1 :=
      product_order _ _ _ _ (fun p m=>raise_order (c.localUnity p m g) (pow_divides (all p m)))
  obtain ⟨n,h⟩:=pow_divides one
  change L=2*n at h
  have sq:=congrArg (fun z:c.F=>z^n) (c.determinant g)
  simp only [CommSemiring.mul_pow,←pow_times,Semiring.one_pow,←h,ch,Semiring.mul_one] at sq
  exact sq

/-- The true order divides the maximal dyadic local exponent, even for an empty support. -/
theorem character_divides {sigma ps : List Nat} {t : Nat} (c : CharacterData sigma ps t) :
    t∣2^totalExponent sigma ps := by
  letI:=c.ring
  let L:=2^totalExponent sigma ps
  apply Nat.dvd_iff_mod_eq_zero.mpr
  change L%t=0
  apply Classical.byContradiction
  intro bad
  have remainder (g : c.Γ) : c.epsilon g^(L%t)=1 := by
    have all : c.epsilon g^L=1 := annihilates c g
    rw [←Nat.mod_add_div L t,Semiring.pow_add,pow_times,c.unity,Semiring.one_pow,Semiring.mul_one] at all
    exact all
  have upper:=c.least _ (show 0<L%t by omega) remainder
  have lower:=Nat.mod_lt L c.orderPos
  omega

theorem divisors_dyadic {t e : Nat} (div : t∣2^e) : ∃k,t=2^k := by
  induction e generalizing t with
  | zero => exact ⟨0,Nat.eq_one_of_dvd_one div⟩
  | succ e ih =>
    rw [Nat.pow_succ] at div
    by_cases even : 2∣t
    · obtain ⟨s,rfl⟩:=even
      rw [Nat.mul_comm 2 s] at div
      obtain ⟨k,h⟩:=ih (Nat.dvd_of_mul_dvd_mul_right (by decide : 0<2) div)
      exact ⟨k+1,by rw [h,Nat.pow_succ,Nat.mul_comm]⟩
    · have gpos:=Nat.gcd_pos_of_pos_right t (by decide : 0<2)
      have upper:=Nat.le_of_dvd (by decide : 0<2) (Nat.gcd_dvd_right t 2)
      have impossible : Nat.gcd t 2≠2 := fun h=>even (h ▸ Nat.gcd_dvd_left t 2)
      have cop : Nat.Coprime t 2 := by change Nat.gcd t 2=1;omega
      exact ih (cop.dvd_of_dvd_mul_right div)

theorem character_dyadic {sigma ps : List Nat} {t : Nat} (c : CharacterData sigma ps t) :
    ∃e,t=2^e := divisors_dyadic (character_divides c)

/-- For order 2^(e+1) the primitive root has degree 2^e. The modular coefficient
field contains its values. These dimension bounds imply the needed multiplicity. -/
theorem character_multiplicity {sigma ps : List Nat} {t gf : Nat} (c : CharacterData sigma ps t)
    (degreePos : 0<gf) (cyclotomicDegree : ∀e,t=2^(e+1) → 2^e≤gf) : t≤2*gf := by
  obtain ⟨k,h⟩:=character_dyadic c
  cases k with
  | zero => simp at h;omega
  | succ e => have q:=cyclotomicDegree e h;rw [h,Nat.pow_succ];omega

theorem character_order {sigma ps : List Nat} {t : Nat} (c : CharacterData sigma ps t) :
    t≤cap sigma ∨ ∃p∈ps,t≤p-1 := by
  let e:=extend (extend 1 sigma) ps
  let L:=2^e
  have every:=annihilates c
  have limit:=c.least L (Nat.pow_pos (by decide)) every
  rcases peak (extend 1 sigma) ps limit with fixed|⟨p,mem,last⟩
  · exact Or.inl fixed
  · by_cases two : p=2
    · apply Or.inl
      rw [two] at last
      exact Nat.le_trans last (Nat.pow_le_pow_right (by decide) (base_le 1 sigma))
    · by_cases tiny : p≤1
      · have low : p-1=0 := by omega
        have z : twos 0=0 := by rw [twos];decide
        rw [localExponent,if_neg two,low,z] at last
        exact Or.inl (Nat.le_trans last (Nat.one_le_pow _ 2 (by decide)))
      · rw [localExponent,if_neg two] at last
        exact Or.inr ⟨p,mem,Nat.le_trans last (Nat.le_of_dvd (by omega) (dyadic_divides _))⟩

end HeightSpecialization.Analytic
