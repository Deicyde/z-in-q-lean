import FourSquares
import CrossRatioForms

/-! The five original charts; in each, the other four branch factors are a
fixed signed integer times a rational square. -/
namespace Sun28.FourContact
open Sun28.Ordinary Sun28.FiveMarkTriples

def rootA (i : Fin 5) : ℤ := ![2400,76800,76832,32,32] i
def rootB (i : Fin 5) : ℤ := ![-225,-375,-343,-343,76832] i
def twistFactor (i : Fin 5) : ℤ := ![343,1,1,1,2] i
def signedTwist (i : Fin 5) : ℤ := twistFactor i*seed (rootA i) (rootB i)
def parameter (i : Fin 5) (x : ℚ) : ℚ :=
  if i=0 then 2401/(x+1) else if i=1 then (x+32)/32 else x/32

def affineForm (i : Fin 5) (s : ℚ) : ℚ :=
  ![1,s,s-1,s-2401,32*s+343] i
def retainedProduct (i : Fin 5) (s : ℚ) : ℚ :=
  ∏ j ∈ Finset.univ.erase i, affineForm j s

private theorem delete_values (i : Fin 5) (f : Fin 5 → ℚ) :
    (∏ j ∈ Finset.univ.erase i,f j) =
      ![f 1*f 2*f 3*f 4, f 0*f 2*f 3*f 4, f 0*f 1*f 3*f 4,
        f 0*f 1*f 2*f 4, f 0*f 1*f 2*f 3] i := by
  fin_cases i
  · change (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 0, f j)=f 1*f 2*f 3*f 4
    rw [show (Finset.univ : Finset (Fin 5)).erase 0={1,2,3,4} by decide]
    norm_num; ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 1, f j)=f 0*f 2*f 3*f 4
    rw [show (Finset.univ : Finset (Fin 5)).erase 1={0,2,3,4} by decide]
    norm_num; ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 2, f j)=f 0*f 1*f 3*f 4
    rw [show (Finset.univ : Finset (Fin 5)).erase 2={0,1,3,4} by decide]
    norm_num; ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 3, f j)=f 0*f 1*f 2*f 4
    rw [show (Finset.univ : Finset (Fin 5)).erase 3={0,1,2,4} by decide]
    norm_num; ring
  · change (∏ j ∈ (Finset.univ : Finset (Fin 5)).erase 4, f j)=f 0*f 1*f 2*f 3
    rw [show (Finset.univ : Finset (Fin 5)).erase 4={0,1,2,3} by decide]
    norm_num; ring

theorem chart_square (i : Fin 5) (x : ℚ) (nx : x+1≠0) :
    ∃ c : ℚ, retainedProduct i (parameter i x)=
      (twistFactor i:ℚ)*cubic (rootA i) (rootB i) x*c^2 := by
  refine ⟨![2401/(x+1)^2,1/32,1/32,1/32,1/256] i,?_⟩
  rw [retainedProduct,delete_values]
  fin_cases i <;> norm_num [affineForm,parameter,twistFactor,cubic,rootA,rootB] <;>
    field_simp [nx] <;> ring

def slope (i : Fin 5) (n : ℕ) : ℚ := parameter i (orbit (rootA i) (rootB i) n)

private theorem denominator_ne (i : Fin 5) (n : ℕ) :
    orbit (rootA i) (rootB i) n+1≠0 := by
  have h:=orbit_avoids_integer (rootA i) (rootB i) (-1) n
  push_cast at h
  exact fun e => h (by linarith)

theorem slope_injective (i : Fin 5) : Function.Injective (slope i) := by
  intro n m h
  apply orbit_injective (rootA i) (rootB i)
  unfold slope parameter at h
  split_ifs at h
  · have e := (div_eq_div_iff (denominator_ne i n) (denominator_ne i m)).mp h
    linarith
  · linarith
  · linarith

theorem literal_product_square (i : Fin 5) (n : ℕ) :
    ∃ v : ℚ, retainedProduct i (slope i n)=(signedTwist i:ℚ)*v^2 := by
  obtain ⟨c,e⟩:=chart_square i _ (denominator_ne i n)
  obtain ⟨v,h⟩:=orbit_square (rootA i) (rootB i) n
  exact ⟨v*c,by rw [slope,e,h,signedTwist];push_cast;ring⟩

theorem twist_nonzero (i : Fin 5) : signedTwist i≠0 := by
  have h : ∀ i : Fin 5, signedTwist i≠0 := by decide
  exact h i

/-- Every prime in a fixed twist is at most 3167, and is inside the actual cutoff. -/
theorem twist_unit {p : ℕ} (hp : p.Prime) (large : 76176<p) (i : Fin 5) :
    ¬ p∣(signedTwist i).natAbs := by
  have factors (u : ℕ) (h : u<76177) (nz : 0<u) : ¬p∣u :=
    fun e => by have := Nat.le_of_dvd nz e; omega
  have catalogue (j : Fin 5) : (signedTwist j).natAbs=
    ![343*(17*29*53*331),19*79*97*3167,233*1319*1373,
      127*1373,2*(127*233*1319)] j := by
    have all : ∀ j : Fin 5, (signedTwist j).natAbs=
      ![343*(17*29*53*331),19*79*97*3167,233*1319*1373,127*1373,2*(127*233*1319)] j := by decide
    exact all j
  rw [catalogue]
  fin_cases i
  · change ¬p∣343*(17*29*53*331)
    simp only [hp.dvd_mul,not_or]
    repeat' apply And.intro
    all_goals exact factors _ (by decide) (by decide)
  · change ¬p∣19*79*97*3167
    simp only [hp.dvd_mul,not_or]
    repeat' apply And.intro
    all_goals exact factors _ (by decide) (by decide)
  · change ¬p∣233*1319*1373
    simp only [hp.dvd_mul,not_or]
    repeat' apply And.intro
    all_goals exact factors _ (by decide) (by decide)
  · change ¬p∣127*1373
    simp only [hp.dvd_mul,not_or]
    repeat' apply And.intro
    all_goals exact factors _ (by decide) (by decide)
  · change ¬p∣2*(127*233*1319)
    simp only [hp.dvd_mul,not_or]
    repeat' apply And.intro
    all_goals exact factors _ (by decide) (by decide)

theorem primitive_form (j : Fin 5) (s : ℚ) :
    (oldForm j s.num s.den : ℚ)=(s.den:ℚ)*affineForm j s := by
  have hn : (s.num:ℚ)=s*s.den := (div_eq_iff (by exact_mod_cast s.den_nz)).mp (Rat.num_div_den s)
  fin_cases j <;> norm_num [oldForm,affineForm] <;> rw [hn] <;> ring

theorem homogeneous_square (i : Fin 5) (n : ℕ) :
    let s:=slope i n
    ∃ v : ℚ, (∏ j ∈ Finset.univ.erase i,(oldForm j s.num s.den:ℚ))=
      (signedTwist i:ℚ)*v^2 := by
  obtain ⟨v,e⟩:=literal_product_square i n
  let s:=slope i n
  refine ⟨(s.den:ℚ)^2*v,?_⟩
  change (∏ j ∈ Finset.univ.erase i,(oldForm j s.num s.den:ℚ))=_
  simp only [primitive_form,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_erase_of_mem
    (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
  change (s.den:ℚ)^4*retainedProduct i (slope i n)=_
  rw [e];ring

end Sun28.FourContact
#print axioms Sun28.FourContact.chart_square
#print axioms Sun28.FourContact.slope_injective
#print axioms Sun28.FourContact.literal_product_square
#print axioms Sun28.FourContact.twist_unit
#print axioms Sun28.FourContact.homogeneous_square
