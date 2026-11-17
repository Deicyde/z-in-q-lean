import DetectorClasses
import RaySelection

namespace Sun28.TwistRank
open ZInQ.RouteK PreparedPoles PairedClasses FixedPreparation ScalarHeight
open Ordinary ContactFactors
noncomputable section

def PrimeShape (β : ℕ) : Prop := ∃ P : Finset ℕ, P.card=5 ∧
    (∀ p∈P,p.Prime ∧ 65<p ∧ p%16=1 ∧ p%7=3) ∧
    (β=∏ p∈P,p ∨ β=17*∏ p∈P,p)

def InputClass (β : ℕ) : Prop := PrimeShape β ∨
    ∃ (X m : ℤ),0 < m ∧ (m:ℚ)∈smallMultipliers ∧
      (β:ℤ)=sqf ((m:ℚ)*((integerRadicand X).natAbs:ℚ))

private theorem reduced_product {m : ℤ} (mp : 0 < m) (member : (m:ℚ)∈smallMultipliers)
    {P : Finset ℕ} (info : ∀ p∈P,p.Prime ∧ 65<p ∧ p%16=1)
    {β : ℕ} (bm : β%24=17) (b6 : β.Coprime 6)
    (spec : (β:ℤ)=sqf ((m:ℚ)*∏ p∈P,(p:ℚ))) :
    β=∏ p∈P,p ∨ β=17*∏ p∈P,p := by
  let n:=m.natAbs
  have eq : (n:ℤ)=m := Int.natAbs_of_nonneg mp.le
  have sn : Squarefree n := Int.squarefree_natAbs.mpr (listed_squarefree member)
  obtain ⟨⟨g,a,b,i⟩,_,mu⟩:=Finset.mem_image.mp member
  change (shift g a b i:ℚ)=(m:ℚ) at mu
  have mi : shift g a b i=m := by exact_mod_cast mu
  have small (l : ℕ) (lp : l.Prime) (dn : l∣n) : l≤23 := by
    have e : n∣primorial := by
      change m.natAbs∣primorial
      rw [←mi]
      exact (show ∀ g a b : Bool,∀ i : Fin 8,(shift g a b i).natAbs∣primorial by decide) g a b i
    have dp := dn.trans e
    rw [←prime_product] at dp
    obtain ⟨s,hs,div⟩:=(Nat.prime_iff.mp lp |>.dvd_finsetProd_iff id).mp dp
    have sp : s.Prime := (show ∀ p∈primes,Nat.Prime p by decide) s hs
    exact ((Nat.prime_dvd_prime_iff_eq lp sp).mp div) ▸ (show ∀ p∈primes,p≤23 by decide) s hs
  have square : Squarefree (∏ p∈P,p) := Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq neq=>Nat.coprime_iff_isRelPrime.mp ((info p hp).1.coprime_iff_not_dvd.mpr
      (fun h=>neq ((Nat.prime_dvd_prime_iff_eq (info p hp).1 (info q hq).1).mp h))))
    (fun p hp=>(info p hp).1.squarefree)
  have cop : n.Coprime (∏ p∈P,p) := by
    by_contra bad
    obtain ⟨l,lp,dn,df⟩:=Nat.Prime.not_coprime_iff_dvd.mp bad
    obtain ⟨p,hp,d⟩:=(Nat.prime_iff.mp lp |>.dvd_finsetProd_iff id).mp df
    have e: l=p := (Nat.prime_dvd_prime_iff_eq lp (info p hp).1).mp d
    exact (not_lt_of_ge (small l lp dn)) (by have := (info p hp).2.1; omega)
  have whole := (Nat.squarefree_mul cop).mpr ⟨sn,square⟩
  have rat : (m:ℚ)*∏ p∈P,(p:ℚ)=((n*∏ p∈P,p:ℕ):ℤ)*(1:ℚ)^2 := by
    have E:(n:ℚ)=m := by exact_mod_cast eq
    push_cast; rw [E]; ring
  have val : β=n*∏ p∈P,p := by
    exact_mod_cast spec.trans (sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr whole) one_ne_zero rat)
  have n6 : n.Coprime 6 := by rw [val,Nat.coprime_mul_iff_left] at b6; exact b6.1
  have E16 : ∏ p∈P,(p:ZMod 8)=1 := Finset.prod_eq_one fun p hp=>by
    have h:= (info p hp).2.2
    apply (ZMod.natCast_eq_natCast_iff' _ 1 8).mpr
    omega
  have e : (β:ZMod 8)=1 := (ZMod.natCast_eq_natCast_iff' _ 1 8).mpr (by omega)
  rw [val,Nat.cast_mul,Nat.cast_prod,E16,mul_one] at e
  have n8 : n%8=1 := (ZMod.natCast_eq_natCast_iff' _ 1 8).mp e
  have possible : n=1 ∨ n=17 := by
    change m.natAbs=1 ∨ m.natAbs=17
    change m.natAbs%8=1 at n8
    change m.natAbs.Coprime 6 at n6
    rw [←mi] at n8 n6 ⊢
    exact (show ∀ g a b : Bool,∀ i : Fin 8,(shift g a b i).natAbs%8=1 →
      (shift g a b i).natAbs.Coprime 6 → (shift g a b i).natAbs=1 ∨ (shift g a b i).natAbs=17
      by decide) g a b i n8 n6
  rcases possible with q|q
  · exact Or.inl (by simpa only [q,one_mul] using val)
  · exact Or.inr (by simpa only [q] using val)

theorem ordinary_prime_shape {A : Fin 3→ℚ} {u v : ℕ} (h : PrimeValues A u v)
    (rays : RayValues h) (vp : 0<v) (j : Fin 3) (nz : A j≠0) {T : ℚ} {m : ℤ} {β θ : ℕ}
    (member : (m:ℚ)∈smallMultipliers)
    (hc : PreparedClasses (detector (A j) (argument A u v j)/T^2) m β θ)
    (pos : 0 < detector (A j) (argument A u v j)/T^2) : PrimeShape β := by
  obtain ⟨a,an,e⟩:=hc.beta_scale
  have hl : 0 < (m:ℚ)*(detector (A j) (argument A u v j)/T^2) := by
    rw [e]; exact mul_pos (by exact_mod_cast hc.beta_positive) (sq_pos_of_ne_zero an)
  have mp : 0 < m := by exact_mod_cast pos_of_mul_pos_left hl pos.le
  have inj : Set.InjOn (fun a : ℚ=>h.value (-a/A j)) (↑marks) := by
    intro x hx y hy z
    exact neg_injective ((div_left_inj' nz).mp (h.injective_on vp (shift_mem A j hx) (shift_mem A j hy) z))
  have cnt : (selected h j).card=5 := by
    rw [selected,Finset.card_image_of_injOn inj]
    norm_num [marks,Finset.card_insert_of_notMem]
  have pr (p : ℕ) (mem : p∈selected h j) : p.Prime ∧ 65<p ∧ p%16=1 ∧ p%7=3 := by
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp mem
    exact ⟨h.prime _ (shift_mem A j hs),rays _ (shift_mem A j hs)⟩
  refine ⟨selected h j,cnt,pr,reduced_product mp member (fun p hp=>⟨(pr p hp).1,(pr p hp).2.1,(pr p hp).2.2.1⟩) hc.beta_mod hc.beta_six ?_⟩
  apply beta_of_scaled_product (z:=scaleFactor (dilation A*v) (argument A u v j)/T) hc
  rw [detector_factorization h vp j nz,div_pow]
  ring

/-- Two quick rejection tests at the ordinary input. The modulus 7
distinguishes the two possible multipliers. -/
theorem prime_shape_residues {β : ℕ} (shape : PrimeShape β) :
    β%16=1 ∧ (β%7=5 ∨ β%7=1) := by
  obtain ⟨P,card,pr,cases⟩:=shape
  have a : ∏ p∈P,(p:ZMod 16)=1 := Finset.prod_eq_one fun p hp=>
    (ZMod.natCast_eq_natCast_iff' _ 1 16).mpr (pr p hp).2.2.1
  have b : ∏ p∈P,(p:ZMod 7)=(3:ZMod 7)^5 := by
    rw [←card,←Finset.prod_const]
    exact Finset.prod_congr rfl fun p hp=>(ZMod.natCast_eq_natCast_iff' _ 3 7).mpr (pr p hp).2.2.2
  rcases cases with rfl|rfl
  · refine ⟨(ZMod.natCast_eq_natCast_iff' _ 1 16).mp ?_,Or.inl ((ZMod.natCast_eq_natCast_iff' _ 5 7).mp ?_)⟩
    · rwa [Nat.cast_prod]
    · rw [Nat.cast_prod,b];decide
  · refine ⟨(ZMod.natCast_eq_natCast_iff' _ 1 16).mp ?_,Or.inr ((ZMod.natCast_eq_natCast_iff' _ 1 7).mp ?_)⟩
    · rw [Nat.cast_mul,Nat.cast_prod,a];decide
    · rw [Nat.cast_mul,Nat.cast_prod,b];decide

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.ordinary_prime_shape

#print axioms Sun28.TwistRank.prime_shape_residues
