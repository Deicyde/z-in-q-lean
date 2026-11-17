import SourceTwists
import ZInQKernel.RouteK.Slots.Multiplier

namespace Sun28.PreparedPoles
open ZInQ.RouteK Sun28.ScalarHeight

/-- Strip at most one factor of a given prime from a squarefree integer. -/
private theorem split_prime (p : ℕ) (hp : p.Prime) (b : ℤ) (hb : Squarefree b) :
    ∃ f : ℤ, ∃ u : ℤ, (f=1 ∨ f=(p:ℤ)) ∧ b=f*u ∧ Squarefree u ∧ ¬(p:ℤ)∣u := by
  by_cases dvd : (p:ℤ)∣b
  · obtain ⟨u,e⟩ := dvd
    refine ⟨p,u,Or.inr rfl,e,(e ▸ hb).of_mul_right,?_⟩
    rintro ⟨t,ht⟩
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (hb _ ⟨t,by rw [e,ht];ring⟩)
  · exact ⟨1,b,Or.inl rfl,(one_mul _).symm,hb,dvd⟩

/-- A square factor prime to six acts trivially on the unit classes modulo 24. -/
private theorem square_unit_mod24 (x : ℤ) (unit2 : ¬(2:ℤ)∣x) (unit3 : ¬(3:ℤ)∣x) :
    x^2 ≡ 1 [ZMOD 24] := by
  have odd : x%2≠0 := by omega
  have three : x%3≠0 := by omega
  have e : x ≡ x%24 [ZMOD 24] := by simp [Int.ModEq]
  have r : x%24=1 ∨ x%24=5 ∨ x%24=7 ∨ x%24=11 ∨ x%24=13 ∨ x%24=17 ∨ x%24=19 ∨ x%24=23 := by omega
  rcases r with h|h|h|h|h|h|h|h <;> (apply (e.pow 2).trans; rw [h]; decide)

private theorem reduced_factor_mod24 {v : ℤ} (v2 : ¬(2:ℤ)∣v) (v3 : ¬(3:ℤ)∣v) :
    ∃ i : Fin 8, ((representatives i : ℤ)*v) % 24=17 := by
  have cases : v%24=1 ∨ v%24=5 ∨ v%24=7 ∨ v%24=11 ∨ v%24=13 ∨ v%24=17 ∨ v%24=19 ∨ v%24=23 := by omega
  rcases cases with h|h|h|h|h|h|h|h
  all_goals first | (refine ⟨0,?_⟩; rw [Int.mul_emod,h]; decide) |
    (refine ⟨1,?_⟩; rw [Int.mul_emod,h]; decide) | (refine ⟨2,?_⟩; rw [Int.mul_emod,h]; decide) |
    (refine ⟨3,?_⟩; rw [Int.mul_emod,h]; decide) | (refine ⟨4,?_⟩; rw [Int.mul_emod,h]; decide) |
    (refine ⟨5,?_⟩; rw [Int.mul_emod,h]; decide) | (refine ⟨6,?_⟩; rw [Int.mul_emod,h]; decide) |
    (refine ⟨7,?_⟩; rw [Int.mul_emod,h]; decide)

private theorem beta_residue {x : ℤ} (hx : 0<x) (h : x%24=17) : sqfInt x%24=17 := by
  obtain ⟨_,u,_,eu⟩ := sqfInt_spec hx.ne'
  have d2 : ¬ (2:ℤ)∣u := by rintro ⟨t,et⟩; have : 2∣x := ⟨sqfInt x*(2*t^2),by linear_combination eu + (sqfInt x)*(u+2*t)*et⟩; omega
  have d3 : ¬ (3:ℤ)∣u := by rintro ⟨t,et⟩; have : 3∣x := ⟨sqfInt x*(3*t^2),by linear_combination eu + (sqfInt x)*(u+3*t)*et⟩; omega
  have mod := (square_unit_mod24 u d2 d3).mul_left (sqfInt x)
  rw [←eu,mul_one] at mod
  change x%24=sqfInt x%24 at mod
  omega

/-- A positive multiplier in Sun's list puts the positive squarefree representative
of μB in the single residue class 17 modulo 24. -/
theorem choose_multiplier {B : ℚ} (pos : 0<B) :
    ∃ m : ℤ, 0 < m ∧ (m:ℚ)∈smallMultipliers ∧
      (∀ p : ℕ, p.Prime → (p:ℤ)∣m → p∈FixedPreparation.primes ∧ ¬(p:ℤ)^2∣m) ∧
      betaOf B m%24=17 := by
  obtain ⟨sf,t,ht,hB⟩ := sqf_spec pos.ne'
  obtain ⟨f,b,hf,eb,sfb,no2⟩ := split_prime 2 Nat.prime_two (sqf B) sf
  obtain ⟨g,v,hg,ev,_,no3⟩ := split_prime 3 Nat.prime_three b sfb
  have no2v : ¬(2:ℤ)∣v := fun h => no2 (ev ▸ dvd_mul_of_dvd_right h _)
  have bp := (sqf_pos_iff pos.ne').2 pos
  have fp : 0<f := by rcases hf with h|h <;> omega
  have gp : 0<g := by rcases hg with h|h <;> omega
  have vp : 0<v := pos_of_mul_pos_right (pos_of_mul_pos_right (by rwa [←ev,←eb] : 0<f*(g*v)) fp.le) gp.le
  obtain ⟨i,hi⟩ := reduced_factor_mod24 no2v no3
  let r : ℤ := representatives i
  have rp : 0<r := by fin_cases i <;> decide
  let m:=f*g*r
  have mp : 0 < m := mul_pos (mul_pos fp gp) rp
  have xeq : (m:ℚ)*B = ((r*v:ℤ):ℚ) * ((f:ℚ)*g*t)^2 := by
    rw [hB,eb,ev]; dsimp [m]; push_cast; ring
  have beta : betaOf B m = sqfInt (r*v) := by
    have f0 : (f:ℚ)≠0 := by exact_mod_cast fp.ne'
    have g0 : (g:ℚ)≠0 := by exact_mod_cast gp.ne'
    rw [betaOf,xeq,sqf_mul_sq (by exact_mod_cast (mul_pos rp vp).ne') (mul_ne_zero (mul_ne_zero f0 g0) ht),sqf_intCast]
  have member (a b : Bool) (j : Fin 8) : (shift false a b j:ℚ)∈smallMultipliers :=
    Finset.mem_image.mpr ⟨(false,a,b,j),Finset.mem_univ _,rfl⟩
  have shape : ∃ a b : Bool, m=shift false a b i := by
    rcases hf with he|he <;> rcases hg with ge|ge
    · exact ⟨false,false,by simp [m,r,he,ge,shift]⟩
    · exact ⟨false,true,by simp [m,r,he,ge,shift]⟩
    · exact ⟨true,false,by simp [m,r,he,ge,shift]⟩
    · exact ⟨true,true,by simp [m,r,he,ge,shift]⟩
  obtain ⟨a,b',em⟩ := shape
  have fixed : ∀ a b : Bool, ∀ j : Fin 8, (shift false a b j)∣223092870 := by decide
  have dm : m∣223092870 := by rw [em]; exact fixed a b' i
  refine ⟨m,mp,by rw [em];exact member a b' i,?_,by rw [beta];exact beta_residue (mul_pos rp vp) hi⟩
  intro p prime div
  have dvd : p∣223092870 := Int.natCast_dvd_natCast.mp (div.trans dm)
  have hp : p∈(223092870:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨prime,dvd,by decide⟩
  have small : (223092870:ℕ).primeFactors=FixedPreparation.primes := by
    change FixedPreparation.primorial.primeFactors=FixedPreparation.primes
    rw [← FixedPreparation.prime_product]
    exact Nat.primeFactors_prod (by decide : ∀ p∈FixedPreparation.primes,p.Prime)
  rw [small] at hp
  refine ⟨hp,?_⟩
  intro pow
  have divides := pow.trans dm
  simp only [FixedPreparation.primes,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at divides
end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.choose_multiplier
