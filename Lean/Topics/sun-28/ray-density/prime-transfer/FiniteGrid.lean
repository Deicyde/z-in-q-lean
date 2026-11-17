import GridRows

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section
variable {n : ℕ} [NeZero n]

def patterns (c : Finset ℤ) (E : Finset (ZMod n)) (H : ZMod n) (W : ℕ) : Finset (ℕ × ZMod n) :=
  ((Icc 1 W) ×ˢ univ).filter fun p => ∀ h ∈ c, p.2+H*(h:ZMod n)*(p.1:ZMod n)^2 ∈ E

private def samples (E : Finset (ZMod n)) (H : ZMod n) (s B T : ℕ) : Finset (ℕ × ZMod n) :=
  ((Icc 1 T) ×ˢ univ).filter fun p => p.2 ∈ good E (H*(p.1:ZMod n)^2) s B

private theorem sum_samples (E : Finset (ZMod n)) (H : ZMod n) (s B T : ℕ) :
    (samples E H s B T).card = ∑ t ∈ Icc 1 T, (good E (H*(t:ZMod n)^2) s B).card := by
  classical
  simp only [samples,card_filter,sum_product]
  apply sum_congr rfl
  intro t _
  rw [←card_filter]
  simp

private theorem samples_to_patterns (c : Finset ℤ) (E : Finset (ZMod n)) (H : ZMod n)
    {s B T : ℕ} (recurs : Recurrent c s B) :
    (samples E H s B T).card ≤ (patterns c E H (B*T)).card*(B*B) := by
  classical
  let S := samples E H s B T
  have each (p : ↥S) : ∃ a : Fin B, ∃ m ∈ Icc 1 B, ∀ h∈c,
      (p.val.2+H*(p.val.1:ZMod n)^2*(a.val:ZMod n))+
        H*(h:ZMod n)*((p.val.1*m:ℕ):ZMod n)^2 ∈ E := by
    have gp := (mem_filter.mp p.property).2
    have enough := (mem_filter.mp gp).2
    obtain ⟨a,m,hm,ok⟩ := recurs _ enough
    refine ⟨a,m,hm,fun h hh => ?_⟩
    obtain ⟨b,hit,eq⟩:=ok h hh
    have bc : (b.val:ZMod n) = (a.val:ZMod n)+(h:ZMod n)*(m:ZMod n)^2 := by
      exact_mod_cast congrArg (fun t : ℤ => (t:ZMod n)) eq
    have hg := (mem_filter.mp hit).2
    change p.val.2 + H*(p.val.1:ZMod n)^2*(b.val:ZMod n) ∈ E at hg
    rw [bc] at hg
    convert hg using 1; push_cast; ring
  choose a m mem_m hit using each
  let f (p : ↥S) := ((p.val.1*m p, p.val.2+H*(p.val.1:ZMod n)^2*((a p).val:ZMod n)),(a p,m p))
  let target := (patterns c E H (B*T)) ×ˢ ((univ : Finset (Fin B)) ×ˢ Icc 1 B)
  have maps (p : ↥S) : f p ∈ target := by
    have time := (mem_Icc.mp (mem_product.mp (mem_filter.mp p.property).1).1)
    have scale := mem_Icc.mp (mem_m p)
    refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,mem_univ _⟩,hit p⟩,
      mem_product.mpr ⟨mem_univ _,mem_m p⟩⟩
    · exact Nat.mul_pos time.1 scale.1
    · simpa only [mul_comm B T] using Nat.mul_le_mul time.2 scale.2
  have inj : Function.Injective f := by
    intro p q eq
    have ma : (a p,m p)=(a q,m q) := congrArg Prod.snd eq
    have aa : a p = a q := congrArg Prod.fst ma
    have mm : m p = m q := congrArg Prod.snd ma
    have fst : p.val.1*m p=q.val.1*m q := congrArg (fun z => z.1.1) eq
    rw [mm] at fst
    have u := Nat.eq_of_mul_eq_mul_right (mem_Icc.mp (mem_m q)).1 fst
    have snd : p.val.2+H*(p.val.1:ZMod n)^2*((a p).val:ZMod n)=
        q.val.2+H*(q.val.1:ZMod n)^2*((a q).val:ZMod n) := congrArg (fun z => z.1.2) eq
    rw [u,aa] at snd
    exact Subtype.ext (Prod.ext u (add_right_cancel snd))
  have card := Fintype.card_le_of_injective (fun p : ↥S => (⟨f p,maps p⟩ : ↥target))
    (fun p q e => inj (congrArg Subtype.val e))
  simpa [S,target] using card

/-- A quantitative finite Varnavides bound with a common multiplicative coefficient H.
Neither invertibility of H nor a lower relation between W and the modulus is required. -/
theorem grid_lower (c : Finset ℤ) (E : Finset (ZMod n)) (H : ZMod n)
    {s B W : ℕ} (hB : 0 < B) (recurs : Recurrent c s B) (density : n ≤ s * E.card)
    (width : 2*B ≤ W) :
    n*W ≤ 4*s*B^3*(patterns c E H W).card := by
  classical
  let T:=W/B
  have down : B*T ≤ W := Nat.mul_div_le W B
  have up : W ≤ 2*(B*T) := by
    have dec := Nat.mod_add_div W B
    have rem := Nat.mod_lt W hB
    change W ≤ 2*(B*(W/B)); omega
  have sample : n*T ≤ 2*s*(samples E H s B T).card := by
    rw [sum_samples,mul_sum]
    have h := sum_le_sum (s:=Icc 1 T) (fun t _ => good_card E (H*(t:ZMod n)^2) hB density)
    simpa [mul_comm n T] using h
  have sub : patterns c E H (B*T) ⊆ patterns c E H W := by
    intro x hx
    obtain ⟨ht,hp⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_product.mp ht).1).1,
      (mem_Icc.mp (mem_product.mp ht).1).2.trans down⟩,mem_univ _⟩,hp⟩
  have maps := (samples_to_patterns c E H recurs (T:=T)).trans
    (Nat.mul_le_mul_right (B*B) (card_le_card sub))
  calc
    n*W ≤ 2*B*(n*T) := by nlinarith only [Nat.mul_le_mul_left n up]
    _ ≤ 2*B*(2*s*((patterns c E H W).card*(B*B))) :=
      Nat.mul_le_mul_left _ (sample.trans (Nat.mul_le_mul_left _ maps))
    _ = _ := by ring

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.grid_lower
