import CharacterOrders
import HeightClosure

namespace HeightSpecialization.Analytic
open IndependentIndices

def fixedPart (sigma : List Nat) := product sigma*plusProduct sigma
def coefficient (a : Nat) (sigma : List Nat) (u : Nat) := 2*a*(2^16*fixedPart sigma)^6*u
def hd3 (a : Nat) (sigma ps : List Nat) (t : Nat) :=
  a*(2^16*fixedPart sigma)^6*((product ps)*(plusProduct ps))^6*t^5

theorem product_pos (ps : List Nat) (lower : ∀p∈ps,0<p) : 0<product ps := by
  induction ps with
  | nil => decide
  | cons p ps ih => exact Nat.mul_pos (lower p (by simp)) (ih (fun q h=>lower q (List.mem_cons_of_mem _ h)))

theorem plus_pos (ps : List Nat) : 0<plusProduct ps := by
  induction ps with
  | nil => decide
  | cons p ps ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem majorize {a t u : Nat} {sigma ps : List Nat}
    (euler : t^5*(plusProduct ps)^6≤u*(product ps)^11) :
    2*hd3 a sigma ps t≤coefficient a sigma u*(product ps)^17 := by
  have en:=Nat.mul_le_mul_left (2*a*(2^16*fixedPart sigma)^6*(product ps)^6) euler
  calc
    _=(2*a*(2^16*fixedPart sigma)^6*(product ps)^6)*(t^5*(plusProduct ps)^6) := by unfold hd3;rw [Nat.mul_pow (product ps) (plusProduct ps) 6];ac_rfl
    _≤_ := en
    _=_ := by unfold coefficient;rw [show (product ps)^17=(product ps)^6*(product ps)^11 from Nat.pow_add (product ps) 6 11];ac_rfl

theorem add_comparison {x n c : Nat} (positive : 0<n) (bound : 2*x≤c*n^17) :
    2*x+128≤(c+128)*n^17 := by
  have base : 128*1≤128*n^17 := Nat.mul_le_mul_left _ (Nat.pow_pos positive)
  rw [Nat.add_mul]
  exact Nat.add_le_add bound (by simpa only [Nat.mul_one] using base)

theorem cm_majorant (sigma ps : List Nat) {a u : Nat} (c0 : 854≤a) (cp : 0<u)
    (sp : ∀p∈sigma,0<p) (mp : ∀p∈ps,0<p) :
    2*(854*(product sigma*product ps))+128≤(coefficient a sigma u+128)*(product ps)^17 := by
  let W:=2^16*fixedPart sigma
  have B:=product_pos sigma sp
  have M:=product_pos ps mp
  have Wpos : 0<W := Nat.mul_pos (by decide) (Nat.mul_pos B (plus_pos sigma))
  have B1 : product sigma≤fixedPart sigma := by
    have := Nat.mul_le_mul_left (product sigma) (plus_pos sigma)
    simpa only [Nat.mul_one,fixedPart] using this
  have B2 : fixedPart sigma≤W := by
    have :=Nat.mul_le_mul_right (fixedPart sigma) (by decide : 1≤2^16)
    simpa only [W,Nat.one_mul] using this
  have B6 : product sigma≤W^6 := Nat.le_trans (Nat.le_trans B1 B2) (by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right Wpos (by decide : 1≤6))
  have c : 2*854*product sigma≤coefficient a sigma u := by
    have start:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 c0) B6
    have last:=Nat.mul_le_mul_left (2*a*W^6) cp
    rw [Nat.mul_one] at last
    exact Nat.le_trans start last
  apply add_comparison M
  have z : product ps≤(product ps)^17 := by simpa only [Nat.pow_one] using Nat.pow_le_pow_right M (by decide : 1≤17)
  have h:=Nat.mul_le_mul c z
  calc _=(2*854*product sigma)*product ps := by ac_rfl
       _≤_ := h

def scalarSet : List Nat := [2,3,5,7,17]
def detectorSet : List Nat := [2,3,5,7,11,13,17,29,37,41,2399]

theorem exact_caps : cap scalarSet=16 ∧ cap detectorSet=16 := by decide +kernel
set_option exponentiation.threshold 8192 in
theorem exact_constants :
    coefficient (2^23) scalarSet ((cap scalarSet)^5)+128=HeightClosure.constant scalarSet ∧
    coefficient (2^23) detectorSet ((cap detectorSet)^5)+128=HeightClosure.constant detectorSet := by rw [exact_caps.1,exact_caps.2];decide

/-- Every repeated variable prime is removed before forming Euler factors. -/
theorem noncm_bound (sigma ps : List Nat) {a t : Nat} (prime : ∀p∈ps,IsContactPrime p)
    (c : CharacterData sigma (support ps) t) :
    2*hd3 a sigma (support ps) t+128≤(coefficient a sigma ((cap sigma)^5)+128)*(radical ps)^17 := by
  have lo (p : Nat) (m : p∈support ps) : 2≤p := (prime p ((mem_support ..).mp m)).1
  have cap2 : 2≤cap sigma := Nat.pow_le_pow_right (by decide : 0<2) (base_le 1 sigma)
  rw [←distinct_product ps prime]
  exact add_comparison (product_pos _ (fun p m=>by have :=lo p m;omega))
    (majorize (euler_absorb _ lo cap2 (character_order c)))

theorem nonempty_bound (sigma ps : List Nat) {a t r u : Nat} (prime : ∀p∈ps,IsContactPrime p)
    (p0 : ∃p,p∈ps) (r2 : 2≤r) (pMin : ∀p∈ps,r≤p) (u2 : 2≤u)
    (ordinary : (cap sigma)^5*(r+1)^6≤u*r^11) (c : CharacterData sigma (support ps) t) :
    2*hd3 a sigma (support ps) t+128≤(coefficient a sigma u+128)*(radical ps)^17 := by
  have lo (p : Nat) (m : p∈support ps) := pMin p ((mem_support ..).mp m)
  obtain ⟨p,hp⟩:=p0
  have nonempty : ∃q,q∈support ps:=⟨p,(mem_support ..).mpr hp⟩
  rw [←distinct_product ps prime]
  exact add_comparison (product_pos _ (fun p m=>by have :=lo p m;omega))
    (majorize (euler_nonempty _ r2 lo nonempty u2 ordinary (character_order c)))

theorem fixed_costs : (cap detectorSet)^5*(19+1)^6≤2*19^11 ∧ (cap scalarSet)^5*(11+1)^6≤11*11^11 := by rw [exact_caps.1,exact_caps.2];decide

end HeightSpecialization.Analytic
