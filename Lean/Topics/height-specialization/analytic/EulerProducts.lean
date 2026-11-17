import ContactRadicals

namespace HeightSpecialization.Analytic
open IndependentIndices

/-- Each distinct prime contributes exactly one Euler factor. -/
def support : List Nat → List Nat
  | [] => []
  | p::ps => if p∈ps then support ps else p::support ps

theorem mem_support (p : Nat) (ps : List Nat) : p∈support ps ↔ p∈ps := by
  induction ps with
  | nil => simp [support]
  | cons a ps ih =>
    by_cases h : a∈ps
    · simp only [support,if_pos h,ih,List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl|q) <;> assumption
    · simp [support,h,ih]

theorem nodup_support (ps : List Nat) : (support ps).Nodup := by
  induction ps with
  | nil => decide
  | cons p ps ih => by_cases h : p∈ps <;> simp [support,h,ih,mem_support]

theorem dvd_radical_of_mem {p : Nat} {ps : List Nat} (member : p∈ps) : p∣radical ps := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons a ps ih =>
    rcases List.mem_cons.mp member with rfl|tail
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih tail) (Nat.dvd_lcm_right ..)

theorem radical_support (ps : List Nat) : radical (support ps)=radical ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p∈ps
    · simp [support,h,radical,ih,Nat.lcm_eq_right (dvd_radical_of_mem h)]
    · simp [support,h,radical,ih]

theorem distinct_product (ps : List Nat) (prime : ∀p∈ps,IsContactPrime p) :
    product (support ps)=radical ps :=
  (prime_list_radical _ (nodup_support _) (fun p h=>prime p ((mem_support ..).mp h))).symm.trans (radical_support ps)

def plusProduct : List Nat → Nat
  | [] => 1
  | p::ps => (p+1)*plusProduct ps

/-- k⁵(p+1)⁶ / p¹¹ decreases as p increases, with all denominators cleared. -/
theorem transport_factor {k c r p : Nat} (pos : 0<r) (le : r≤p)
    (first : k^5*(r+1)^6≤c*r^11) : k^5*(p+1)^6≤c*p^11 := by
  have frac : r*(p+1)≤p*(r+1) := by rw [Nat.mul_add,Nat.mul_add,Nat.mul_one,Nat.mul_one,Nat.mul_comm p r];omega
  have f:=Nat.pow_le_pow_left frac 6
  rw [Nat.mul_pow,Nat.mul_pow] at f
  have h : k^5*(p+1)^6*r^6≤c*p^11*r^6 := calc
    _=k^5*(r^6*(p+1)^6) := by ac_rfl
    _≤k^5*(p^6*(r+1)^6) := Nat.mul_le_mul_left _ f
    _=(k^5*(r+1)^6)*p^6 := by ac_rfl
    _≤c*r^11*p^6 := Nat.mul_le_mul_right _ first
    _=(c*p^6*r^6)*r^5 := by rw [show 11=6+5 by decide,Nat.pow_add];ac_rfl
    _≤(c*p^6*r^6)*p^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le 5)
    _=c*p^11*r^6 := by rw [show 11=6+5 by decide,Nat.pow_add];ac_rfl
  exact Nat.le_of_mul_le_mul_right h (Nat.pow_pos pos)

theorem ordinary_factor (p : Nat) (h : 2≤p) : (p+1)^6≤p^11 := by
  simpa using transport_factor (k:=1) (c:=1) (r:=2) (by decide) h (by decide)

/-- At a prime carrying the maximal dyadic order, (p−1)⁵(p+1)⁶ ≤ 2p¹¹. -/
theorem distinguished_factor {t p : Nat} (hp : 2≤p) (size : t≤p-1) : t^5*(p+1)^6≤2*p^11 := by
  have mult : (p-1)*(p+1)≤p^2 := by
    obtain ⟨n,e⟩:=Nat.exists_eq_add_of_le hp
    subst p
    have diff : 2+n-1=n+1 := by omega
    have eq : (n+1)*(2+n+1)+1=(2+n)^2 := by grobner
    rw [diff];omega
  calc
    _≤(p-1)^5*(p+1)^6 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left size 5)
    _=((p-1)*(p+1))^5*(p+1) := by rw [Nat.mul_pow,show (p+1)^6=(p+1)^5*(p+1) from Nat.pow_succ ..];ac_rfl
    _≤(p^2)^5*(p+1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left mult 5)
    _≤(p^2)^5*(2*p) := Nat.mul_le_mul_left _ (by omega)
    _=2*p^11 := by grobner

private theorem factor_product {a b c d k t x y : Nat}
    (h : t*a≤k*b) (h' : c≤d) (e : x^6=a*c) (f : y^11=b*d) : t*x^6≤k*y^11 := by
  rw [e,f,←Nat.mul_assoc,←Nat.mul_assoc]
  exact Nat.mul_le_mul h h'

theorem ordinary_product (ps : List Nat) (lower : ∀p∈ps,2≤p) : (plusProduct ps)^6≤(product ps)^11 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    rw [plusProduct,product,Nat.mul_pow,Nat.mul_pow]
    exact Nat.mul_le_mul (ordinary_factor p (lower p (by simp))) (ih (fun q h=>lower q (List.mem_cons_of_mem _ h)))

theorem one_distinguished (ps : List Nat) (lower : ∀p∈ps,2≤p) {t c : Nat}
    (pick : ∃p∈ps, t^5*(p+1)^6≤c*p^11) : t^5*(plusProduct ps)^6≤c*(product ps)^11 := by
  induction ps with
  | nil => obtain ⟨p,bad,_⟩:=pick;exact False.elim (List.not_mem_nil bad)
  | cons q qs ih =>
    obtain ⟨p,member,h⟩:=pick
    have tail : ∀j∈qs,2≤j := fun j hj=>lower j (List.mem_cons_of_mem _ hj)
    rcases List.mem_cons.mp member with rfl|mem
    · exact factor_product h (ordinary_product qs tail) (Nat.mul_pow ..) (Nat.mul_pow ..)
    · have r:=ih tail ⟨p,mem,h⟩
      apply factor_product r (ordinary_factor q (lower q (by simp)))
      · rw [plusProduct,Nat.mul_pow,Nat.mul_comm]
      · rw [product,Nat.mul_pow,Nat.mul_comm]

/-- The elementary part of (HD3), for every list including the empty support. -/
theorem euler_absorb (ps : List Nat) (lower : ∀p∈ps,2≤p) {t k : Nat} (k2 : 2≤k)
    (character : t≤k ∨ ∃p∈ps,t≤p-1) :
    t^5*(plusProduct ps)^6≤k^5*(product ps)^11 := by
  rcases character with small|⟨p,mem,size⟩
  · exact Nat.mul_le_mul (Nat.pow_le_pow_left small _) (ordinary_product ps lower)
  · apply one_distinguished ps lower
    have bound : 2≤k^5 := Nat.le_trans (by decide : 2≤2^5) (Nat.pow_le_pow_left k2 _)
    exact ⟨p,mem,Nat.le_trans (distinguished_factor (lower p mem) size) (Nat.mul_le_mul_right _ bound)⟩

/-- On nonempty support the fixed exceptional character can also be paid for at one variable prime. -/
theorem euler_nonempty (ps : List Nat) {r k c t : Nat} (minp : 2≤r) (lower : ∀p∈ps,r≤p)
    (existsPrime : ∃p,p∈ps) (c2 : 2≤c) (fixedCost : k^5*(r+1)^6≤c*r^11)
    (character : t≤k ∨ ∃p∈ps,t≤p-1) : t^5*(plusProduct ps)^6≤c*(product ps)^11 := by
  apply one_distinguished ps (fun p hp=>Nat.le_trans minp (lower p hp))
  rcases character with small|⟨p,mem,size⟩
  · obtain ⟨p,hp⟩:=existsPrime
    exact ⟨p,hp,Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left small _))
      (transport_factor (by omega) (lower p hp) fixedCost)⟩
  · exact ⟨p,mem,Nat.le_trans (distinguished_factor (Nat.le_trans minp (lower p mem)) size) (Nat.mul_le_mul_right _ c2)⟩

end HeightSpecialization.Analytic
