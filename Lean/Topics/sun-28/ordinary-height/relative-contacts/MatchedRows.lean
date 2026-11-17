import ContactClasses

/-! Two equal squareclasses give a divisor of the fixed difference squared.
The resulting bound does not involve the numerator of the common multiplier. -/
namespace Sun28.RelativeContacts
open Sun28.Ordinary Height
noncomputable section

/-- Integer factors with square product differ by a nonzero fixed integer. -/
theorem factors_of_square_product {f g : ℤ} (ne : f≠g) (h : IsSquare (f*g)) :
    |f|≤(f-g)^2 ∧ |g|≤(f-g)^2 := by
  obtain ⟨w,sw⟩:=h
  have hw : 0≤f*g := by rw [sw];exact mul_self_nonneg _
  let P:=f+g-2*w
  let Q:=f+g+2*w
  have eqn : P*Q=(f-g)^2 := by dsimp [P,Q];nlinarith only [sw]
  have pos : 0<(f-g)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ne)
  have absprod : |P| *|Q|=(f-g)^2 := by rw [←abs_mul,eqn,abs_of_pos pos]
  have p1 : 1≤|P| := by
    have pn : P≠0 := fun z=>by rw [z,zero_mul] at eqn;omega
    have := abs_pos.mpr pn;omega
  have q1 : 1≤|Q| := by
    have qn : Q≠0 := fun z=>by rw [z,mul_zero] at eqn;omega
    have := abs_pos.mpr qn;omega
  have bp : |P|≤(f-g)^2 := (le_mul_of_one_le_right (abs_nonneg P) q1).trans_eq absprod
  have bq : |Q|≤(f-g)^2 := by rw [←absprod,mul_comm]; exact le_mul_of_one_le_right (abs_nonneg Q) p1
  have tr:=abs_add_le P Q
  rw [show P+Q=2*(f+g) by dsimp [P,Q];ring,abs_mul] at tr
  have sum : |f+g|≤(f-g)^2 := by norm_num at tr;omega
  have same : 0≤f ∧ 0≤g ∨ f≤0 ∧ g≤0 := by
    rcases eq_or_ne f 0 with h|h
    · subst f;rcases le_total 0 g with v|v <;> simp [*]
    rcases eq_or_ne g 0 with h|h
    · subst g;rcases le_total 0 f with v|v <;> simp [*]
    rcases lt_or_gt_of_ne (show f≠0 by assumption) with hf|hf <;>
      rcases lt_or_gt_of_ne (show g≠0 by assumption) with hg|hg
    · exact Or.inr ⟨hf.le,hg.le⟩
    · exact (not_lt_of_ge hw (mul_neg_of_neg_of_pos hf hg)).elim
    · exact (not_lt_of_ge hw (mul_neg_of_pos_of_neg hf hg)).elim
    · exact Or.inl ⟨hf.le,hg.le⟩
  rcases same with ⟨hf,hg⟩|⟨hf,hg⟩
  · rw [abs_of_nonneg (add_nonneg hf hg)] at sum
    rw [abs_of_nonneg hf,abs_of_nonneg hg];omega
  · rw [abs_of_nonpos (add_nonpos hf hg)] at sum
    rw [abs_of_nonpos hf,abs_of_nonpos hg];omega

private theorem denom_ident (z : ℚ) : z*(z.den:ℚ)=z.num :=
  (eq_div_iff (by exact_mod_cast z.den_nz)).mp (Rat.num_div_den z).symm

/-- Two translated scale values in the same nonzero squareclass, with integer
mark numerators i,j in a common positive denominator L. -/
theorem matched_scaled {s η : ℚ} (en : η≠0) {L i j : ℤ} (lp : 0<L) (ij:i≠j)
    (pair : IsSquare (relativeForm s η ((i:ℚ)/L)*relativeForm s η ((j:ℚ)/L))) :
    L*|η.num| *s.num^2 ≤ (i-j)^2*((η.den:ℤ)*s.den^2)^2+|i| *((η.den:ℤ)*s.den^2) := by
  let K:ℤ:=(η.den:ℤ)*s.den^2
  let M:ℤ:=L*η.num*s.num^2
  let F:ℤ:=M-i*K
  let G:ℤ:=M-j*K
  have kp:0<K := by dsimp [K];positivity
  have Mne : F≠G := by
    intro eqn
    have bad : (i-j)*K=0 := by dsimp [F,G] at eqn;linear_combination -eqn
    exact (mul_ne_zero (sub_ne_zero.mpr ij) kp.ne') bad
  let D:ℚ:=(L:ℚ)*η.num*s.den^2
  have conv (a:ℤ) : (M-a*K:ℤ)=D*relativeForm s η ((a:ℚ)/L) := by
    have zd : (s.den:ℚ)≠0 := by exact_mod_cast s.den_nz
    have ed : (η.den:ℚ)≠0 := by exact_mod_cast η.den_nz
    have em : (η.num:ℚ)≠0 := by exact_mod_cast Rat.num_ne_zero.mpr en
    have ll : (L:ℚ)≠0 := by exact_mod_cast lp.ne'
    dsimp [D,M,K,relativeForm]
    push_cast
    have zz := denom_ident s
    have ee := denom_ident η
    field_simp
    linear_combination -(L:ℚ)*η.num*η*((s.den:ℚ)*s+s.num)*zz - a*(s.den:ℚ)^2*ee
  have fs : IsSquare (F*G) := by
    apply Rat.isSquare_intCast_iff.mp
    rw [Int.cast_mul]
    change IsSquare (((M-i*K:ℤ):ℚ)*((M-j*K:ℤ):ℚ))
    rw [conv i,conv j]
    obtain ⟨w,hw⟩:=pair
    refine ⟨D*w,?_⟩
    linear_combination D^2*hw
  have h1:=(factors_of_square_product Mne fs).1
  have sub : F-G=(j-i)*K := by dsimp [F,G];ring
  have we : |M|≤ |F|+|i| *K := by
    calc
      _ = |F+i*K| := by congr 1;dsimp [F];ring
      _ ≤ _ := by simpa only [abs_mul,abs_of_pos kp] using abs_add_le F (i*K)
  rw [sub,mul_pow,show (j-i)^2=(i-j)^2 by ring] at h1
  have m : |M|=L*|η.num| *s.num^2 := by dsimp [M];rw [abs_mul,abs_mul,abs_of_pos lp,abs_of_nonneg (sq_nonneg s.num)]
  rw [m] at we
  change _ ≤ (i-j)^2*K^2+|i| *K
  omega

private theorem height_of_num {s : ℚ} {C K : ℤ} (C1 : 1≤C) (K1 : 1≤K)
    (den : (s.den:ℤ)≤K) (num : s.num^2≤C*K^2) :
    2*logHeight₁ s ≤ Real.log (C:ℝ)+2*Real.log (K:ℝ) := by
  let H : ℕ:=max s.num.natAbs s.den
  have hi : (H:ℤ)^2 ≤ C*K^2 := by
    rcases le_total s.num.natAbs s.den with hn|hn
    · dsimp [H];rw [max_eq_right hn]
      have first:=pow_le_pow_left₀ (Int.natCast_nonneg _) den 2
      exact first.trans (le_mul_of_one_le_left (sq_nonneg _) C1)
    · dsimp [H];rw [max_eq_left hn,Int.natCast_natAbs,sq_abs];exact num
  have hpos : 0<H := s.den_pos.trans_le (le_max_right _ _)
  have hc : 0<(C:ℝ) := by exact_mod_cast (show 0<C by omega)
  have hk : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hi' : (H:ℝ)^2 ≤ (C:ℝ)*(K:ℝ)^2 := by exact_mod_cast hi
  have log:=Real.log_le_log (pow_pos (by exact_mod_cast hpos : (0:ℝ)<H) 2) hi'
  rw [Real.log_mul hc.ne' (pow_pos hk 2).ne',Real.log_pow,Real.log_pow] at log
  simpa only [Rat.logHeight₁_eq_log_max,H,Nat.cast_ofNat] using log

private theorem den_le {s η : ℚ} : (s.den:ℤ)≤(η.den:ℤ)*s.den^2 := by
  have e1:(1:ℤ)≤η.den := by exact_mod_cast η.den_pos
  have bd1:(1:ℤ) ≤ (s.den:ℤ) := by exact_mod_cast s.den_pos
  calc
    _ ≤ (s.den:ℤ)^2 := by nlinarith only [bd1,sq_nonneg ((s.den:ℤ)-1)]
    _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) e1

private theorem mark_encoding (a : ℚ) (ha : a∈marks) :
    ∃ j : ℤ, a=(j:ℚ)/1952786 ∧ |j|≤1952786 := by
  simp only [marks,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,by norm_num,by norm_num⟩
  · exact ⟨-976393,by norm_num,by norm_num⟩
  · exact ⟨-1952786,by norm_num,by norm_num⟩
  · exact ⟨814,by norm_num,by norm_num⟩
  · exact ⟨-153536,by norm_num,by norm_num⟩

/-- At least one of the ten unordered pairs has equal squareclasses. -/
def Matched (s η : ℚ) : Prop :=
  ∃ a∈marks, ∃ b∈marks, a≠b ∧ IsSquare (relativeForm s η a*relativeForm s η b)

/-- A cap on the height of a matched scale in terms of two denominators. -/
theorem matched_height {s η : ℚ} (en:η≠0) (matchPair:Matched s η) :
    2*logHeight₁ s≤Real.log 3905573+2*Real.log ((η.den:ℝ)*s.den^2) := by
  obtain ⟨a,ha,b,hb,diff,pair⟩:=matchPair
  obtain ⟨i,ai,ism⟩:=mark_encoding a ha
  obtain ⟨j,bj,jsm⟩:=mark_encoding b hb
  have small : |i-j|≤1953600 := by
    have range (r:ℚ) (hm:r∈marks) (z:ℤ) (eq:r=(z:ℚ)/1952786) :
        -1952786≤z ∧ z≤814 := by
      have rat : (-1:ℚ)≤r ∧ r≤1/2399 := by
        simp only [marks,Finset.mem_insert,Finset.mem_singleton] at hm
        rcases hm with rfl|rfl|rfl|rfl|rfl <;> norm_num
      rw [eq] at rat
      have low:(-1952786:ℚ)≤z := by linarith
      have high:(z:ℚ)≤814 := by linarith
      exact ⟨by exact_mod_cast low,by exact_mod_cast high⟩
    obtain ⟨il,ih⟩:=range _ ha _ ai
    obtain ⟨jl,jh⟩:=range _ hb _ bj
    exact abs_le.mpr ⟨by omega,by omega⟩
  have neq : i≠j := by intro h;rw [ai,bj,h] at diff;exact diff rfl
  rw [ai,bj] at pair
  have h:=matched_scaled en (L:=1952786) (i:=i) (j:=j) (by decide) neq (by simpa using pair)
  let K:ℤ:=(η.den:ℤ)*s.den^2
  have K1:1≤K := by
    have pos : 0<K := by dsimp [K];positivity
    omega
  have e1:1≤|η.num| := by have p:=abs_pos.mpr (Rat.num_ne_zero.mpr en);omega
  have lo := mul_le_mul_of_nonneg_right (show (1952786:ℤ)≤1952786*|η.num| by omega) (sq_nonneg s.num)
  have diffSq:=pow_le_pow_left₀ (abs_nonneg (i-j)) small 2
  rw [sq_abs] at diffSq
  have hdiff:=mul_le_mul_of_nonneg_right diffSq (sq_nonneg K)
  have hi:=mul_le_mul_of_nonneg_right ism (show 0≤K by omega)
  have KK:K≤K^2 := by nlinarith only [K1,sq_nonneg (K-1)]
  change _≤(i-j)^2*K^2+|i| *K at h
  have bn:s.num^2≤3905573*K^2 := by nlinarith only [lo,h,hdiff,hi,KK,sq_nonneg K]
  have q:=height_of_num (s:=s) (C:=3905573) (K:=K) (by decide) K1 den_le bn
  simpa [K] using q

/-- For the two consecutive negative marks the coefficient disappears. -/
theorem adjacent_num {s η : ℚ} (en:η≠0)
    (pair : IsSquare (relativeForm s η (-1/2)*relativeForm s η (-1))) :
    s.num^2≤((η.den:ℤ)*s.den^2)^2 := by
  have h:=matched_scaled en (L:=2) (i:=-1) (j:=-2) (by decide) (by decide) (by norm_num at pair ⊢; exact pair)
  let K:ℤ:=(η.den:ℤ)*s.den^2
  change _≤K^2
  have K1:1≤K := by
    have pos : 0<K := by dsimp [K];positivity
    omega
  have e1:1≤|η.num| := by have p:=abs_pos.mpr (Rat.num_ne_zero.mpr en);omega
  have lo:=mul_le_mul_of_nonneg_right (show (2:ℤ)≤2*|η.num| by omega) (sq_nonneg s.num)
  have KK:K≤K^2 := by nlinarith only [K1,sq_nonneg (K-1)]
  change 2*|η.num| *s.num^2≤(-1-(-2))^2*K^2+|-1| *K at h
  norm_num only at h
  nlinarith only [h,lo,KK]

end
end Sun28.RelativeContacts
#print axioms Sun28.RelativeContacts.factors_of_square_product
#print axioms Sun28.RelativeContacts.matched_scaled
#print axioms Sun28.RelativeContacts.matched_height
#print axioms Sun28.RelativeContacts.adjacent_num
