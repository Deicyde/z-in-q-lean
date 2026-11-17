import LogProjection

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.WeightedSelection Finset Filter Topology
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

/-- Unweighted count in the full numerical sample, with a failed test at this prime. -/
def oneCount (T : Finset ℕ) (κ p : ℕ) (S : Finset (Record A d H Y)) :=
  (S.filter (fun a=>¬atPrime a.gaussian T κ p)).card

theorem middle_card (T : Finset ℕ) (κ L R : ℕ) (S : Finset (Record A d H Y))
    (M : ℝ) (non : 0≤M) (major : ∀ a∈S,weight a≤M) :
    middleMass T κ L R S ≤ M*∑ p∈places L R,(oneCount T κ p S:ℝ) := by
  let B:=S.filter (fun a=>below a T κ L ∧ ¬below a T κ R)
  let bad:=fun p=>S.filter (fun a=>¬atPrime a.gaussian T κ p)
  have cover : B⊆(places L R).biUnion bad := by
    intro a ha
    obtain ⟨mem,passed,failed⟩:=mem_filter.mp ha
    simp only [below,not_forall] at failed
    obtain ⟨p,pp,odd,seven,hi,obs⟩:=failed
    exact mem_biUnion.mpr ⟨p,mem_places.mpr ⟨lt_of_not_ge (fun lo=>obs (passed p pp odd seven lo)),hi,pp⟩,
      mem_filter.mpr ⟨mem,obs⟩⟩
  have count : B.card≤∑ p∈places L R,oneCount T κ p S := (card_le_card cover).trans card_biUnion_le
  change ∑ a∈B,weight a ≤ _
  calc _ ≤ ∑ _∈B,M := sum_le_sum fun a ha=>major a (mem_filter.mp ha).1
       _ = M*(B.card:ℝ) := by simp [mul_comm]
       _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast count) non

theorem reciprocal_squares (L R : ℕ) (pos : 0<L) :
    (∑ p∈places L R,1/(p:ℝ)^2)≤1/(L:ℝ) := by
  let f:=fun p : ℕ=>1/((p:ℝ)-1)-1/(p:ℝ)
  have whole : (∑ p∈Ioc L R,f p) =
      (if L≤R then 1/(L:ℝ)-1/(R:ℝ) else 0) := by
    induction R with
    | zero => simp [show ¬ L≤0 by omega]
    | succ r ih =>
      by_cases lo : L≤r
      · rw [Finset.sum_Ioc_succ_top lo,ih,ite_eq_left lo,ite_eq_left (by omega)]
        dsimp [f];push_cast;ring_nf
      · by_cases eq : L=r+1
        · subst L; simp
        · simp [Finset.Ioc_eq_empty_of_le (show r+1≤L by omega),show ¬ L≤r+1 by omega]
  have bound (p : ℕ) (h : L<p) : 1/(p:ℝ)^2 ≤ f p := by
    have hp : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
    dsimp [f];field_simp
    nlinarith
  calc _ ≤ ∑ p∈places L R,f p := sum_le_sum fun p hp=>bound p (mem_places.mp hp).1
       _ ≤ ∑ p∈Ioc L R,f p := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
          fun p hp _ => (by positivity : (0:ℝ)≤1/(p:ℝ)^2).trans (bound p (mem_Ioc.mp hp).1)
       _ ≤ _ := by rw [whole];split_ifs <;> have h := (show (0:ℝ)≤1/(R:ℝ) by positivity) <;> have h' := (show (0:ℝ)≤1/(L:ℝ) by positivity) <;> linarith

/-- A sufficient pointwise unweighted sieve estimate. The starting height may depend on the row and
cutoff. One nonnegative error bound works simultaneously for all primes in the indicated range. -/
def PrimeRow (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ L J : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ,J≤j → ∃ D : ℝ,0≤D ∧ ∀ᶠ t : ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    let X:ℝ:=(N:ℝ)*W
    let G:ℝ:=growthBound A t
    ∀ p∈places L (logCutoff A t),
      (oneCount T κ p (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W):ℝ) ≤
        C*X/((p:ℝ)^2*G^(shifts A).card)+D*X/(2:ℝ)^t

theorem poly_error (A : Fin 3→ℚ) (D : ℝ) (non : 0≤D) :
    Tendsto (fun t=>D*(growthBound A t:ℝ)^(2*(shifts A).card+5)/(2:ℝ)^t) atTop (𝓝 0) := by
  let m:=2*(shifts A).card+5
  let c:=envelope A+404
  have h:=(tendsto_pow_const_div_const_pow_of_one_lt m (by norm_num : (1:ℝ)<2)).const_mul (D*(c:ℝ)^m)
  rw [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun _=>by positivity) _ h
  filter_upwards [eventually_ge_atTop (1:ℕ)] with t ht
  have l : growthBound A t≤c*t := by
    dsimp [growthBound,growth,c];nlinarith only [Nat.mul_le_mul_left (envelope A) ht,ht]
  have pr : (growthBound A t:ℝ)^m ≤ (c:ℝ)^m*(t:ℝ)^m := by rw [←mul_pow];exact_mod_cast Nat.pow_le_pow_left l m
  change D*(growthBound A t:ℝ)^m/(2:ℝ)^t ≤ (D*(c:ℝ)^m)*((t:ℝ)^m/2^t)
  rw [←mul_div_assoc,mul_assoc];gcongr
end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.middle_card
#print axioms Sun28.MediumSieve.reciprocal_squares
#print axioms Sun28.MediumSieve.poly_error
