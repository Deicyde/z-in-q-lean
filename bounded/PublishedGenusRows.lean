import TwistLFunction

open Finset
open scoped BigOperators

namespace ZInQBlueprint.OriginalRank.PublishedGenusRows

open ZInQBlueprint.TYZ
open ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b

def AllOne (R : Finset ℕ) : Prop := ∀ x ∈ R, x % 8 = 1

/-- The first unordered index of TYZ Theorem 1.4. -/
def FirstRow (F : Finset ℕ) : Prop := ∃ a ∈ F, AllOne (F.erase a)

/-- The second unordered index of TYZ Theorem 1.4. An absent second
factor is allowed when all remaining factors are one modulo eight. -/
def MixedRow (F : Finset ℕ) : Prop :=
  ∃ a ∈ F, (a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7) ∧
    (AllOne (F.erase a) ∨
      ∃ b ∈ F.erase a, (b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3) ∧
        AllOne ((F.erase a).erase b))

private theorem prod_one (R : Finset ℕ) (hr : AllOne R) : (∏ x ∈ R, x) % 8 = 1 := by
  induction R using Finset.induction_on with
  | empty => decide
  | @insert a R ha ih =>
    rw [prod_insert ha, Nat.mul_mod, hr a (mem_insert_self _ _),
      ih (fun x hx => hr x (mem_insert_of_mem hx))]

private theorem first_mod {d a : ℕ} {F : Finset ℕ} (hd : d % 8 = 5)
    (hp : ∏ x ∈ F, x = d) (ha : a ∈ F) (hR : AllOne (F.erase a)) : a % 8 = 5 := by
  have h := congrArg (fun m : ℕ => m % 8) ((F.mul_prod_erase (fun x => x) ha).trans hp)
  change (a * (∏ x ∈ F.erase a, x)) % 8 = d % 8 at h
  simpa [Nat.mul_mod, prod_one _ hR, hd] using h

private theorem pair_mod {a b : ℕ} (ha : a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7)
    (hb : b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3) (h : (a % 8 * (b % 8)) % 8 = 5) :
    (a % 8 = 5 ∧ b % 8 = 1) ∨ (a % 8 = 7 ∧ b % 8 = 3) := by
  rcases ha with p | p | p <;> rcases hb with q | q | q
  all_goals first | exact Or.inl ⟨p,q⟩ | exact Or.inr ⟨p,q⟩ | (rw [p,q] at h; norm_num at h)

/-- The second sufficient condition in Ye Tian, Notices ICCM 5 (2017),
Theorem 4.7, page 58. Its two displayed factors both have to occur. -/
def TianSecond (F : Finset ℕ) : Prop :=
  ∃ a ∈ F, (a % 8 = 5 ∨ a % 8 = 7) ∧
    ∃ b ∈ F.erase a, (b % 8 = 2 ∨ b % 8 = 3) ∧ AllOne ((F.erase a).erase b)

private theorem mixed_of_second {F : Finset ℕ} (h : TianSecond F) : MixedRow F := by
  obtain ⟨a,ha,ham,b,hb,hbm,hr⟩ := h
  exact ⟨a,ha,ham.imp_right Or.inr,Or.inr ⟨b,hb,Or.inr hbm,hr⟩⟩

private theorem second_of_residues {d : ℕ} {F : Finset ℕ} (hd : d % 8 = 5)
    (hF : F ∈ factorizations d) (hR : Residues F) : TianSecond F := by
  obtain ⟨T, hT⟩ := BracketTerm.exists_of_factors hd (mem_filter.mpr ⟨hF,hR⟩)
  have h7 := T.d₀mod
  have h3 := T.second_mod hd
  have hab : T.d₀ ≠ T.d₁ := by intro he; rw [he] at h7; omega
  have haR : T.d₀ ∉ T.rest := fun h => by have := (T.rest_factors _ h).2; omega
  have hbR : T.d₁ ∉ T.rest := fun h => by have := (T.rest_factors _ h).2; omega
  have hn : T.d₀ ∉ insert T.d₁ T.rest := by simp [hab,haR]
  have hA : T.factors.erase T.d₀ = insert T.d₁ T.rest := by simp [BracketTerm.factors,hn]
  rw [← hT]
  refine ⟨T.d₀, mem_insert_self _ _, Or.inr h7, ?_⟩
  refine ⟨T.d₁, by rw [hA]; exact mem_insert_self _ _, Or.inr h3, ?_⟩
  rw [hA, erase_insert hbR]
  exact fun x hx => (T.rest_factors x hx).2

/-- In residue five the mixed index is the union of the first row and the
index of the second bracket on page 760. This is an equality of predicates
on factorizations. It does not count a choice among factors of residue one. -/
theorem mixed_iff {d : ℕ} {F : Finset ℕ} (hd : d % 8 = 5) (hF : F ∈ factorizations d) :
    MixedRow F ↔ FirstRow F ∨ Residues F := by
  obtain ⟨hlt,hp⟩ := (mem_factorizations (by omega) F).mp hF
  constructor
  · rintro ⟨a,ha,ham,hrest⟩
    rcases hrest with hall | ⟨b,hb,hbm,hr⟩
    · exact Or.inl ⟨a,ha,hall⟩
    · let R := (F.erase a).erase b
      have decomp : a * b * (∏ x ∈ R, x) = d := by
        rw [Nat.mul_assoc]
        change a * (b * (∏ x ∈ (F.erase a).erase b, x)) = d
        rw [(F.erase a).mul_prod_erase (fun x => x) hb, F.mul_prod_erase (fun x => x) ha, hp]
      have h := congrArg (fun m : ℕ => m % 8) decomp
      change (a * b * (∏ x ∈ R, x)) % 8 = d % 8 at h
      rw [Nat.mul_mod, Nat.mul_mod a b, prod_one R hr, mul_one, Nat.mod_mod, hd] at h
      rcases pair_mod ham hbm h with ⟨_,hb1⟩ | ⟨ha7,hb3⟩
      · refine Or.inl ⟨a,ha,?_⟩
        intro x hx
        by_cases he : x = b
        · simpa only [he] using hb1
        · exact hr x (mem_erase.mpr ⟨he,hx⟩)
      · let T : BracketTerm d :=
          ⟨a,b,R,ha7,Or.inr hb3,hlt b (mem_erase.mp hb).2,
           fun x hx => ⟨hlt x (mem_erase.mp (mem_erase.mp hx).2).2,hr x hx⟩,decomp⟩
        have he : T.factors = F := by
          change insert a (insert b ((F.erase a).erase b)) = F
          rw [insert_erase hb, insert_erase ha]
        have hv : T.factors ∈ admissibleFactorizations d := (bracketEquiv d hd T).property
        rw [he] at hv
        exact Or.inr (mem_filter.mp hv).2
  · rintro (⟨a,ha,hr⟩ | h)
    · exact ⟨a,ha,Or.inl (first_mod hd hp ha hr),Or.inl hr⟩
    · exact mixed_of_second (second_of_residues hd hF h)

theorem disjoint_rows {d : ℕ} {F : Finset ℕ} (hd : d % 8 = 5) (hF : F ∈ factorizations d)
    (h : FirstRow F) : ¬ Residues F := by
  rintro ⟨_,_,all⟩
  obtain ⟨a,ha,hR⟩ := h
  have h5 := first_mod hd ((mem_factorizations (by omega) F).mp hF).2 ha hR
  rcases all a ha with v | v | v <;> omega

/-- On positive squarefree inputs of residue five, Tian’s second criterion is
exactly the class-seven/class-three bracket. The combinatorics here works
for every factor set whose product is five modulo eight. -/
theorem tian_second_iff {d : ℕ} {F : Finset ℕ} (hd : d % 8 = 5) (hF : F ∈ factorizations d) :
    TianSecond F ↔ Residues F := by
  constructor
  · intro h
    rcases (mixed_iff hd hF).mp (mixed_of_second h) with hFirst | hR
    · obtain ⟨a,_,_,b,hb,hbm,_⟩ := h
      obtain ⟨c,hc,hr⟩ := hFirst
      have hc5 := first_mod hd ((mem_factorizations (by omega) F).mp hF).2 hc hr
      by_cases he : b = c
      · rw [he] at hbm
        omega
      · have h1 := hr b (mem_erase.mpr ⟨he,(mem_erase.mp hb).2⟩)
        omega
    · exact hR
  · exact second_of_residues hd hF

noncomputable def rowSum (d : ℕ) (P : Finset ℕ → Prop) : ℕ := by
  classical
  exact ∑ F ∈ factorizations d, if P F then ∏ x ∈ F, genusNumber x else 0

/-- An identity of natural numbers, before reducing the two printed sums modulo two. -/
theorem mixed_sum_eq {d : ℕ} (hd : d % 8 = 5) :
    rowSum d MixedRow = rowSum d FirstRow + printedCoefficient d hd := by
  classical
  rw [printedCoefficient_eq_integerCoefficient hd, rowSum, rowSum, integerCoefficient,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  have hi := mixed_iff hd hF
  by_cases h1 : FirstRow F
  · have hm := hi.mpr (Or.inl h1)
    have hr := disjoint_rows hd hF h1
    simp [h1,hm,hr]
  · by_cases hr : Residues F
    · have hm := hi.mpr (Or.inr hr)
      simp [h1,hm,hr]
    · have hm : ¬ MixedRow F := fun h => (hi.mp h).elim h1 hr
      simp [h1,hm,hr]

/-- Literal comparison with the separate second sum of Tian's published
Theorem 4.7. Both sides count each unordered factorization exactly once. -/
theorem tian_second_sum_eq {d : ℕ} (hd : d % 8 = 5) :
    rowSum d TianSecond = printedCoefficient d hd := by
  classical
  rw [printedCoefficient_eq_integerCoefficient hd, rowSum, integerCoefficient]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hr : Residues F
  · simp [hr,(tian_second_iff hd hF).mpr hr]
  · have ht : ¬ TianSecond F := fun h => hr ((tian_second_iff hd hF).mp h)
    simp [hr,ht]

/-- TYZ page 722, the higher-order branch of the definition; F is the
continuation of the arithmetic Hasse–Weil L-function of the printed cubic. -/
def HigherOrderNormalization (Lcal : ℕ → ℤ) : Prop :=
  ∀ (d : ℕ), d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F → 2 ≤ analyticOrderAt F 1 → Lcal d = 0

/-- Evenness of the normalized rational number is precisely integral
divisibility by the next power of two, including exponent zero. -/
theorem normalized_even_iff (z : ℤ) (r : ℕ) :
    (∃ k : ℤ, (z : ℚ) / (2 : ℚ) ^ r = 2 * (k : ℚ)) ↔ (2 : ℤ) ^ (r + 1) ∣ z := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    have eq := (div_eq_iff (by positivity : (2 : ℚ) ^ r ≠ 0)).mp hk
    calc
      z = 2 * k * (2 : ℤ) ^ r := by exact_mod_cast eq
      _ = (2 : ℤ) ^ (r + 1) * k := by rw [pow_succ]; ring
  · rintro ⟨k,hk⟩
    refine ⟨k,(div_eq_iff (by positivity)).mpr ?_⟩
    have eq : z = 2 * k * (2 : ℤ) ^ r := by rw [hk,pow_succ]; ring
    exact_mod_cast eq

/-- TYZ Theorem 1.4, pp. 723–724, interpreted with the singleton retained
in the second row. Page 752 of the proof explicitly includes that term. -/
def AJM14Singleton (Lcal : ℕ → ℤ) (rho : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    (∃ k : ℤ, (Lcal d : ℚ) / (2 : ℚ) ^ rho d = 2 * (k : ℚ)) →
    Even (rowSum d FirstRow) ∧ Even (rowSum d MixedRow)

/-- Only the higher-order zero branch and the two congruences of the
published theorem are needed for the selected-twist input. -/
theorem higher_order_of_ajm14_singleton (Lcal : ℕ → ℤ) (rho : ℕ → ℕ)
    (normalized : HigherOrderNormalization Lcal) (published : AJM14Singleton Lcal rho) :
    HigherOrderGenusCoefficient := by
  intro d hd hs F hF order
  have hz := normalized d hd hs F hF order
  have divisible : (2 : ℤ) ^ (rho d + 1) ∣ Lcal d := hz ▸ dvd_zero _
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := published d hd hs ((normalized_even_iff _ _).2 divisible)
  have h := mixed_sum_eq hd
  exact ⟨b - a, by omega⟩

/-- The signed integer in the lower-order branches is left as data. The only
branch used in this application is exactly the zero branch on TYZ page 722. -/
noncomputable def normalized (lower : ℕ → ℤ) (d : ℕ) : ℤ := by
  classical
  exact if ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧
    2 ≤ analyticOrderAt F 1 then 0 else lower d

theorem zero_branch (lower : ℕ → ℤ) : HigherOrderNormalization (normalized lower) := by
  intro d _ _ F hF order
  exact ite_eq_left ⟨F,hF,order⟩

/-- Alternative via the two AJM congruences with their singleton convention. -/
theorem selected_of_ajm14_singleton (lower : ℕ → ℤ) (rho : ℕ → ℕ)
    (published : AJM14Singleton (normalized lower) rho) : HigherOrderGenusCoefficient :=
  higher_order_of_ajm14_singleton _ rho (zero_branch lower) published

/-- Ye Tian, Notices ICCM 5 (2017), Theorem 4.7, specialized to squarefree d
of residue five. Oddness of either printed genus sum implies oddness of
the normalized rational number as an integer. -/
def Tian47 (Lcal : ℕ → ℤ) (rho : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Odd (rowSum d FirstRow) ∨ Odd (rowSum d TianSecond)) →
    ∃ k : ℤ, (Lcal d : ℚ) / (2 : ℚ) ^ rho d = 2 * (k : ℚ) + 1

/-- The consequence of Tian's Theorem 4.7 needed here. Only the higher-order
branch is fixed. The lower-order values and index exponent are existential data. -/
def PublishedTian47 : Prop :=
  ∃ (lower : ℕ → ℤ) (rho : ℕ → ℕ), Tian47 (normalized lower) rho

theorem higher_order_of_tian47 (source : PublishedTian47) : HigherOrderGenusCoefficient := by
  obtain ⟨lower,rho,published⟩ := source
  intro d hd hs F hF order
  by_contra he
  have odd : Odd (rowSum d TianSecond) := by
    rw [tian_second_sum_eq hd]
    exact Nat.not_even_iff_odd.mp he
  obtain ⟨k,hk⟩ := published d hd hs (Or.inr odd)
  have hz := zero_branch lower d hd hs F hF order
  have hq : (0 : ℚ) = 2 * (k : ℚ) + 1 := by simpa [hz] using hk
  have hi : (0 : ℤ) = 2 * k + 1 := by exact_mod_cast hq
  omega

end ZInQBlueprint.OriginalRank.PublishedGenusRows

#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.mixed_iff
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.disjoint_rows
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.mixed_sum_eq
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.higher_order_of_ajm14_singleton

#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.normalized_even_iff
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.zero_branch
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.selected_of_ajm14_singleton

#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.tian_second_iff
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.tian_second_sum_eq
#print axioms ZInQBlueprint.OriginalRank.PublishedGenusRows.higher_order_of_tian47
