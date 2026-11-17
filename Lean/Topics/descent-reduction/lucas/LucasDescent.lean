import ZeroInput

namespace LucasDescent
open ZeroInput

/-- The quadratic equation for two consecutive Lucas terms. -/
def Sol (a x y : Int) : Prop := x^2 + y^2 = a*x*y + 1

theorem lucas_step (a : Int) (n : Nat) :
    lucas a (n+1) = ((lucas a n).2, a*(lucas a n).2-(lucas a n).1) := by
  simp [lucas]

theorem recurrence_sol (a : Int) (n : Nat) : Sol a (lucas a n).1 (lucas a n).2 := by
  induction n with
  | zero => simp [lucas, Sol]
  | succ n ih =>
    rw [lucas_step]
    change (lucas a n).2^2+(a*(lucas a n).2-(lucas a n).1)^2 =
      a*(lucas a n).2*(a*(lucas a n).2-(lucas a n).1)+1
    unfold Sol at ih
    grobner

theorem increasing (a : Int) (ha : 3 ≤ a) (n : Nat) :
    0 ≤ (lucas a n).1 ∧ (lucas a n).1 < (lucas a n).2 := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    rw [lucas_step]
    dsimp
    have upper := Int.mul_le_mul_of_nonneg_right ha (show 0 ≤ (lucas a n).2 by omega)
    omega

/-- The predecessor of a positive ordered solution is integral and strictly smaller. -/
theorem smaller_root {a x y : Int} (hx : 0 < x) (hxy : x ≤ y) (h : Sol a x y) :
    0 ≤ a*x-y ∧ a*x-y < x ∧ Sol a (a*x-y) x := by
  unfold Sol at h ⊢
  have pid : (a*x-y)*y = x*x-1 := by grobner
  have hy : 0 < y := by omega
  have xx := Int.mul_le_mul_of_nonneg_left (show 1 ≤ x by omega) (show 0 ≤ x by omega)
  have xxy := Int.mul_le_mul_of_nonneg_left hxy (show 0 ≤ x by omega)
  simp only [Int.mul_one] at xx
  refine ⟨?_, ?_, ?_⟩
  · apply Int.le_of_not_gt
    intro hn
    have := Int.mul_neg_of_neg_of_pos hn hy
    omega
  · apply Int.lt_of_mul_lt_mul_right (a := y) _ (by omega)
    omega
  · grobner

/-- Classification, with descent measured by the nonnegative smaller coordinate. -/
theorem ordered_to_lucas {a x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) (h : Sol a x y) :
    ∃ n : Nat, lucas a n = (x,y) := by
  by_cases zero : x = 0
  · subst x
    have he : y*y = 1 := by simpa [Sol,Int.pow_succ] using h
    have hy : 0 < y := by
      by_cases hz : y = 0
      · simp [hz] at he
      · omega
    have hpos := Int.mul_le_mul_of_nonneg_left (show 1 ≤ y by omega) hxy
    simp only [Int.mul_one] at hpos
    have : y = 1 := by omega
    exact ⟨0, by simp [lucas,this]⟩
  · have ⟨hz, hlt, pred⟩ := smaller_root (show 0 < x by omega) hxy h
    obtain ⟨n,hn⟩ := ordered_to_lucas hz (Int.le_of_lt hlt) pred
    refine ⟨n+1,?_⟩
    rw [lucas_step,hn]
    simp
    omega
termination_by x.toNat
decreasing_by omega

/-- For a ≥ 3, the positive orbit starts at (0,1) and visits exactly
the ordered nonnegative integral solutions. -/
theorem ordered_iff {a x y : Int} (ha : 3 ≤ a) :
    (0 ≤ x ∧ x ≤ y ∧ Sol a x y) ↔ (∃ n : Nat, lucas a n = (x,y)) := by
  constructor
  · rintro ⟨hx,hxy,h⟩
    exact ordered_to_lucas hx hxy h
  · rintro ⟨n,hn⟩
    have hpos := increasing a ha n
    have hs := recurrence_sol a n
    rw [hn] at hpos hs
    exact ⟨hpos.1,Int.le_of_lt hpos.2,hs⟩


/-- U₀=0 and U₁=1, using the first projection of the existing pair recurrence. -/
abbrev U (a : Int) (n : Nat) : Int := (lucas a n).1

private theorem next_term (a : Int) (n : Nat) : U a (n+1) = (lucas a n).2 := by
  simp [U,lucas_step]

theorem either_order {a x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : Sol a x y) :
    ∃ n, (x = U a n ∧ y = U a (n+1)) ∨ (y = U a n ∧ x = U a (n+1)) := by
  by_cases hxy : x ≤ y
  · obtain ⟨n, hn⟩ := ordered_to_lucas hx hxy h
    exact ⟨n,Or.inl ⟨(congrArg Prod.fst hn).symm,
      (congrArg Prod.snd hn).symm.trans (next_term a n).symm⟩⟩
  · have hs : Sol a y x := by unfold Sol at *; grobner
    obtain ⟨n, hn⟩ := ordered_to_lucas hy (by omega) hs
    exact ⟨n,Or.inr ⟨(congrArg Prod.fst hn).symm,
      (congrArg Prod.snd hn).symm.trans (next_term a n).symm⟩⟩

/-- Congruence at a−2, including its divisibility converse. -/
theorem dvd_minus_two (a : Int) (n : Nat) : a-2 ∣ U a n ↔ a-2 ∣ (n:Int) := by
  have h := (lucas_divided (a-2) n).1
  rw [show a-2+2=a by omega] at h
  apply Int.dvd_iff_dvd_of_dvd_sub
  exact ⟨(difference (a-2) n).1, by unfold U; omega⟩

theorem neg_parameter (a : Int) (n : Nat) :
    (lucas (-a) n).1 = -((-1:Int)^n)*(lucas a n).1 ∧
    (lucas (-a) n).2 = (-1:Int)^n*(lucas a n).2 := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    rcases ih with ⟨h,k⟩
    simp only [lucas_step,Int.pow_succ]
    constructor <;> grobner

private theorem sign_pow (n : Nat) : (-1:Int)^n = 1 ∨ (-1:Int)^n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Int.pow_succ]
    rcases ih with h|h <;> simp [h]

/-- Congruence at the negative double root, expressed as exact divisibility. -/
theorem dvd_plus_two (a : Int) (n : Nat) : a+2 ∣ U a n ↔ a+2 ∣ (n:Int) := by
  have h := dvd_minus_two (-a) n
  rw [show -a-2= -(a+2) by omega, Int.neg_dvd, Int.neg_dvd] at h
  have eqn := (neg_parameter a n).1
  rcases sign_pow n with hs|hs
  · simp only [hs,Int.neg_one_mul] at eqn
    change (a+2 ∣ (lucas a n).1) ↔ _
    change (a+2 ∣ (lucas (-a) n).1) ↔ _ at h
    simpa only [eqn,Int.dvd_neg] using h
  · simp only [hs,Int.neg_neg,Int.one_mul] at eqn
    change (a+2 ∣ (lucas (-a) n).1) ↔ _ at h
    simpa only [eqn] using h

theorem term_increases (a : Int) (ha : 3 ≤ a) (n : Nat) : U a n < U a (n+1) := by
  rw [next_term]
  exact (increasing a ha n).2

theorem term_mono (a : Int) (ha : 3 ≤ a) {m n : Nat} (hmn : m ≤ n) :
    U a m ≤ U a n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => exact Int.le_refl _
  | succ k ih =>
    exact Int.le_trans ih (Int.le_of_lt (term_increases a ha (m+k)))

/-- A real logarithm is unnecessary for the recurrence's growth estimate. -/
theorem term_growth (a : Int) (ha : 3 ≤ a) (n : Nat) :
    (a-1)^n ≤ U a (n+1) := by
  induction n with
  | zero => simp [U,lucas]
  | succ n ih =>
    rw [Int.pow_succ]
    have mul := Int.mul_le_mul_of_nonneg_right ih (show 0 ≤ a-1 by omega)
    have step := term_increases a ha n
    have recur : U a (n+2) = a*U a (n+1)-U a n := by
      rw [next_term a (n+1),lucas_step]; rw [next_term]
    rw [recur]
    have form : U a (n+1)*(a-1) = a*U a (n+1)-U a (n+1) := by grobner
    rw [form] at mul
    omega

private theorem square_magnitude (x : Int) : ((x.natAbs:Int))^2 = x^2 := by
  rcases Int.natAbs_eq x with e|e <;> grobner

/-- Taking magnitudes is justified by the equation even for a negative parameter. -/
theorem signed_magnitudes {a x y : Int} (h : Sol a x y) :
    Sol (a.natAbs:Int) (x.natAbs:Int) (y.natAbs:Int) := by
  have px : 0 ≤ x^2 := Int.pow_nonneg_of_even (by decide)
  have py : 0 ≤ y^2 := Int.pow_nonneg_of_even (by decide)
  have prod_nn : 0 ≤ a*x*y := by
    by_cases h0 : x=0
    · simp [h0]
    · have hxpos : 0 < x.natAbs := Int.natAbs_pos.mpr h0
      have hs : 0 < ((x.natAbs:Int))^2 := Int.pow_pos (by omega)
      rw [square_magnitude] at hs
      unfold Sol at h; omega
  have pp := Int.natAbs_of_nonneg prod_nn
  simp only [Int.natAbs_mul,Int.natCast_mul] at pp
  unfold Sol at h ⊢
  rw [square_magnitude,square_magnitude,pp]; exact h


private theorem index_dvd (a : Int) (d n : Nat)
    (side : (d:Int) = a-2 ∨ (d:Int) = a+2) :
    (d:Int) ∣ U a n ↔ d ∣ n := by
  rw [← Int.ofNat_dvd]
  rcases side with h|h
  · simpa only [h] using dvd_minus_two a n
  · simpa only [h] using dvd_plus_two a n

/-- If the distinguished coordinate is a positive multiple of d=a±2,
the smallest two possible coordinates are its index-d term and preceding term. -/
theorem least_neighbor {a : Int} {d : Nat} (ha : 3 ≤ a)
    (side : (d:Int) = a-2 ∨ (d:Int) = a+2)
    {x y : Int} (hx : 0 ≤ x) (hy : 0 < y) (dy : (d:Int) ∣ y) (h : Sol a x y) :
    U a (d-1) ≤ x ∧ U a d ≤ y := by
  have bound : ∀ i, y = U a i → d ≤ i := by
    intro i he
    have ip : 0 < i := by
      by_cases h0 : i=0
      · simp [h0,U,lucas] at he; omega
      · omega
    exact Nat.le_of_dvd ip ((index_dvd a d i side).mp (he ▸ dy : (d:Int) ∣ U a i))
  obtain ⟨n, hn⟩ := either_order hx (Int.le_of_lt hy) h
  rcases hn with ⟨xx,yy⟩|⟨yy,xx⟩
  · have hi := bound (n+1) yy
    rw [xx,yy]
    exact ⟨term_mono a ha (by omega),term_mono a ha hi⟩
  · have hi := bound n yy
    rw [xx,yy]
    exact ⟨term_mono a ha (by omega),term_mono a ha hi⟩

private theorem term_positive (a : Int) (ha : 3 ≤ a) {n : Nat} (hp : 0 < n) :
    0 < U a n := by
  have h := term_mono a ha (m := 1) (n := n) (by omega)
  have h1 : U a 1 = 1 := rfl
  omega

/-- Both minimum bounds are attained by one positive solution. -/
theorem attained_neighbor {a : Int} {d : Nat} (ha : 3 ≤ a) (hd : 2 ≤ d)
    (side : (d:Int) = a-2 ∨ (d:Int) = a+2) :
    let x := U a (d-1)
    let z := U a d / (d:Int)
    0 < x ∧ 0 < z ∧ (d:Int)*z = U a d ∧ Sol a x ((d:Int)*z) := by
  dsimp only
  have hdiv : (d:Int) ∣ U a d := (index_dvd a d d side).mpr (Nat.dvd_refl d)
  have prodEq := Int.ediv_mul_cancel hdiv
  rw [Int.mul_comm] at prodEq
  have uy := term_positive a ha (n := d) (by omega)
  have zp : 0 < U a d / (d:Int) :=
    Int.pos_of_mul_pos_right (by rwa [prodEq]) (by omega : 0 < (d:Int))
  refine ⟨term_positive a ha (by omega),zp,prodEq,?_⟩
  rw [prodEq]
  have sols := recurrence_sol a (d-1)
  rw [← next_term a (d-1), show d-1+1 = d by omega] at sols
  exact sols

/-- The literal signed equation in the manuscript. -/
def LabelSol (s t z : Int) : Prop := t^2 - s*(s-2)*t*z + (s-2)^2*z^2 = 1

private theorem parameter_sides {s : Int} (ha : 7 ≤ s.natAbs) :
    let a := (s.natAbs:Int)
    let d := ((s-2).natAbs:Int)
    (d = a-2 ∨ d = a+2) ∧ s*(s-2) = a*d ∧ 2 ≤ d := by
  dsimp only
  by_cases hpos : 0 ≤ s
  · have as := Int.natAbs_of_nonneg hpos
    have hs : 0 ≤ s-2 := by omega
    rw [as,Int.natAbs_of_nonneg hs]
    exact ⟨Or.inl rfl,rfl,by omega⟩
  · have as := Int.ofNat_natAbs_of_nonpos (show s ≤ 0 by omega)
    have ds := Int.ofNat_natAbs_of_nonpos (show s-2 ≤ 0 by omega)
    rw [as,ds]
    exact ⟨Or.inr (by omega),by grobner,by omega⟩

/-- Uniform signed lower bounds in the literal equation, excluding z=0 exactly as in the paper. -/
theorem signed_minima {s t z : Int} (ha : 7 ≤ s.natAbs) (hz : z ≠ 0)
    (h : LabelSol s t z) :
    let a := (s.natAbs:Int)
    let d := (s-2).natAbs
    U a (d-1) ≤ (t.natAbs:Int) ∧ U a d ≤ (d:Int)*(z.natAbs:Int) := by
  dsimp only
  obtain ⟨side,_,hd⟩ := parameter_sides ha
  have raw : Sol s t ((s-2)*z) := by unfold Sol LabelSol at *; grobner
  have norm := signed_magnitudes raw
  simp only [Int.natAbs_mul,Int.natCast_mul] at norm
  have zp := Int.natAbs_pos.mpr hz
  exact least_neighbor (by omega) side (Int.natCast_nonneg _)
    (Int.mul_pos (by omega) (by omega)) ⟨_,rfl⟩ norm

/-- For either sign of s the chosen quotient is positive and solves the signed equation. -/
theorem signed_attained (s : Int) (ha : 7 ≤ s.natAbs) :
    let a := (s.natAbs:Int)
    let d := (s-2).natAbs
    let t := U a (d-1)
    let z := U a d / (d:Int)
    0 < t ∧ 0 < z ∧ LabelSol s t z := by
  dsimp only
  obtain ⟨side,hprod,hd⟩ := parameter_sides ha
  obtain ⟨hp,zp,_,norm⟩ := attained_neighbor (by omega) (by omega) side
  refine ⟨hp,zp,?_⟩
  unfold LabelSol
  unfold Sol at norm
  have hsq := square_magnitude (s-2)
  grobner


/-- Exactly the two exceptional points when the last label is zero. -/
theorem zero_label (s t : Int) : LabelSol s t 0 ↔ t = 1 ∨ t = -1 := by
  constructor
  · intro h
    have he : (t-1)*(t+1)=0 := by unfold LabelSol at h; grobner
    rcases Int.mul_eq_zero.mp he with e|e
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (rfl|rfl) <;> simp [LabelSol]

private theorem integer_exponential (b : Int) (hb : 6 ≤ b) (n : Nat) :
    (3:Int)^(2+n+1) < b^(2+n) := by
  induction n with
  | zero =>
    have h₁ := Int.mul_le_mul_of_nonneg_right hb (by omega : 0 ≤ b)
    have h₂ := Int.mul_le_mul_of_nonneg_left hb (by decide : (0:Int) ≤ 6)
    change (27:Int) < b^2
    rw [Int.pow_succ,Int.pow_one]
    omega
  | succ n ih =>
    change (3:Int)^(2+n+1+1) < b^(2+n+1)
    rw [Int.pow_succ 3 (2+n+1),Int.pow_succ b (2+n)]
    have l := Int.mul_lt_mul_of_pos_right ih (by decide : (0:Int)<3)
    have r := Int.mul_le_mul_of_nonneg_left (by omega : (3:Int)≤b)
      (Int.pow_nonneg (m := 2+n) (by omega : 0 ≤ b))
    exact Int.lt_of_lt_of_le l r

/-- Strong integer form of the manuscript's exponential lower bound. -/
theorem signed_growth {s t z : Int} (ha : 7 ≤ s.natAbs) (hz : z ≠ 0)
    (h : LabelSol s t z) :
    (3:Int)^(s.natAbs-3) < ((s.natAbs:Int)-1)^(s.natAbs-4) ∧
    ((s.natAbs:Int)-1)^(s.natAbs-4) ≤ (t.natAbs:Int) := by
  obtain ⟨side,_,_⟩ := parameter_sides ha
  have hi : s.natAbs-4+1 ≤ (s-2).natAbs-1 := by rcases side with e|e <;> omega
  have low := (signed_minima ha hz h).1
  have mid := term_mono (s.natAbs:Int) (by omega) hi
  have top := term_growth (s.natAbs:Int) (by omega) (s.natAbs-4)
  have cmp := integer_exponential ((s.natAbs:Int)-1) (by omega) (s.natAbs-6)
  rw [show 2+(s.natAbs-6) = s.natAbs-4 by omega,
      show s.natAbs-4+1 = s.natAbs-3 by omega] at cmp
  exact ⟨cmp,Int.le_trans top (Int.le_trans mid low)⟩

private theorem parameter_congruence (m a b : Int) (parameters : m ∣ a-b) (n : Nat) :
    (m ∣ (lucas a n).1-(lucas b n).1) ∧ (m ∣ (lucas a n).2-(lucas b n).2) := by
  obtain ⟨q,hq⟩ := parameters
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    rcases ih with ⟨⟨v,hv⟩,⟨w,hw⟩⟩
    simp only [lucas_step]
    exact ⟨⟨w,hw⟩,⟨a*w+q*(lucas b n).2-v, by grobner⟩⟩

private theorem six_step (n : Nat) : lucas 1 (n+6) = lucas 1 n := by
  change lucas 1 ((((((n+1)+1)+1)+1)+1)+1) = lucas 1 n
  apply Prod.ext <;> simp only [lucas_step] <;> grobner

private theorem two_residues (k : Nat) : U 1 (6*k+4) = -1 ∧ U 1 (6*k+5) = -1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 6*(k+1)+4=6*k+4+6 by omega,show 6*(k+1)+5=6*k+5+6 by omega]
    change (lucas 1 (6*k+4+6)).1 = -1 ∧ (lucas 1 (6*k+5+6)).1 = -1
    rw [six_step,six_step]; exact ih

/-- The least positive labels at s₀=6(k+1), a=s₀+1: t≡−1, z≡1 modulo s₀. -/
theorem least_residues (k : Nat) :
    let m := (6*(k+1):Nat)
    let a := (m:Int)+1
    let d := 6*k+5
    (m:Int) ∣ (U a (d-1)+1 : Int) ∧ (m:Int) ∣ (U a d / (d:Int)-1 : Int) := by
  dsimp only
  let m : Int := ((6*(k+1):Nat):Int)
  let d := 6*k+5
  change (m ∣ U (m+1) (d-1)+1) ∧ (m ∣ U (m+1) d / (d:Int)-1)
  have relation : (d:Int) = (m+1)-2 := by dsimp [d,m]; omega
  have div := attained_neighbor (a := m+1) (d := d) (by dsimp [m]; omega)
    (by dsimp [d]; omega) (Or.inl relation)
  have c := parameter_congruence m (m+1) 1 (⟨1,by grobner⟩)
  have c₁ := (c (d-1)).1
  have c₂ := (c d).1
  have vals := two_residues k
  have first : U 1 (d-1) = -1 := by
    change U 1 (6*k+5-1) = -1
    rw [show 6*k+5-1=6*k+4 by omega]; exact vals.1
  change m ∣ U (m+1) (d-1) - U 1 (d-1) at c₁
  change m ∣ U (m+1) d - U 1 d at c₂
  rw [first] at c₁
  rw [show U 1 d = -1 from vals.2] at c₂
  obtain ⟨q,hq⟩ := c₂
  exact ⟨by simpa only [Int.sub_neg] using c₁,⟨U (m+1) d / (d:Int)-q,by
    have prodEq := div.2.2.1
    grobner⟩⟩


/-- The two complete congruences Uₙ≡n and Uₙ≡−(−1)ⁿn at the double roots ±2. -/
theorem double_root_congruences (a : Int) (n : Nat) :
    (a-2 ∣ U a n-(n:Int)) ∧ (a+2 ∣ U a n+(-1:Int)^n*(n:Int)) := by
  have two : U 2 n = (n:Int) := by simpa only [Int.zero_add,Int.zero_mul,Int.add_zero] using
    (lucas_divided 0 n).1
  have neg := (neg_parameter 2 n).1
  change U (-2) n = -((-1:Int)^n)*U 2 n at neg
  rw [two] at neg
  have pos := (parameter_congruence (a-2) a 2 ⟨1,by grobner⟩ n).1
  have negp := (parameter_congruence (a+2) a (-2) ⟨1,by grobner⟩ n).1
  change a-2 ∣ U a n-U 2 n at pos
  change a+2 ∣ U a n-U (-2) n at negp
  rw [two] at pos; rw [neg] at negp
  exact ⟨pos,by simpa only [Int.neg_mul,Int.sub_neg] using negp⟩

/-- Both extremal coordinates are minimal, including after taking the quotient. -/
theorem signed_minimum_quotient {s t z : Int} (ha : 7 ≤ s.natAbs) (hz : z ≠ 0)
    (h : LabelSol s t z) :
    let a := (s.natAbs:Int)
    let d := (s-2).natAbs
    U a (d-1) ≤ (t.natAbs:Int) ∧ U a d/(d:Int) ≤ (z.natAbs:Int) := by
  dsimp only
  obtain ⟨left,right⟩ := signed_minima ha hz h
  obtain ⟨side,_,hd⟩ := parameter_sides ha
  have prodEq := (attained_neighbor (by omega) (by omega) side).2.2.1
  refine ⟨left,(Int.mul_le_mul_left (by omega : 0 < ((s-2).natAbs:Int))).mp ?_⟩
  rw [prodEq]; exact right

/-- No ordered solution occurs twice in the list. -/
theorem orbit_injective {a : Int} (ha : 3 ≤ a) {m n : Nat}
    (h : lucas a m = lucas a n) : m=n := by
  have he : U a m = U a n := congrArg Prod.fst h
  have strict : ∀ {i j : Nat}, i < j → U a i < U a j := by
    intro i j hij
    exact Int.lt_of_lt_of_le (term_increases a ha i) (term_mono a ha (by omega : i+1≤j))
  by_cases small : m<n
  · have := strict small; omega
  · by_cases large : n<m
    · have := strict large; omega
    · omega

/-- The sign condition lost when taking absolute values is both necessary and sufficient. -/
theorem signed_iff (a x y : Int) :
    Sol a x y ↔ 0 ≤ a*x*y ∧ Sol (a.natAbs:Int) (x.natAbs:Int) (y.natAbs:Int) := by
  have absprod : ((a*x*y).natAbs:Int) = (a.natAbs:Int)*(x.natAbs:Int)*(y.natAbs:Int) := by
    simp only [Int.natAbs_mul,Int.natCast_mul]
  constructor
  · intro h
    have norm := signed_magnitudes h
    refine ⟨?_,norm⟩
    unfold Sol at h norm
    rw [square_magnitude,square_magnitude,← absprod] at norm
    have nn := Int.natCast_nonneg (a*x*y).natAbs
    omega
  · rintro ⟨nn,h⟩
    unfold Sol at h ⊢
    rwa [square_magnitude,square_magnitude,← absprod,Int.natAbs_of_nonneg nn] at h

/-- The divisibility statements for the actual scalar family give two odd least labels. -/
theorem least_labels_odd (k : Nat) :
    let m := 6*(k+1)
    let a := (m:Int)+1
    let d := 6*k+5
    U a (d-1)%2 = 1 ∧ (U a d/(d:Int))%2 = 1 := by
  dsimp only
  let m : Int := ((6*(k+1):Nat):Int)
  let d := 6*k+5
  let t := U (m+1) (d-1)
  let z := U (m+1) d/(d:Int)
  change t%2=1 ∧ z%2=1
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := least_residues k
  change t + 1 = m*i at hi
  change z - 1 = m*j at hj
  have even : m=2*(3*((k:Int)+1)) := by dsimp [m]; omega
  have ht : t=2*((3*((k:Int)+1))*i)-1 := by grobner
  have hz : z=2*((3*((k:Int)+1))*j)+1 := by grobner
  omega

end LucasDescent

#print axioms LucasDescent.smaller_root
#print axioms LucasDescent.ordered_iff
#print axioms LucasDescent.orbit_injective
#print axioms LucasDescent.either_order
#print axioms LucasDescent.double_root_congruences
#print axioms LucasDescent.dvd_minus_two
#print axioms LucasDescent.dvd_plus_two
#print axioms LucasDescent.term_growth
#print axioms LucasDescent.signed_magnitudes
#print axioms LucasDescent.least_neighbor
#print axioms LucasDescent.attained_neighbor
#print axioms LucasDescent.signed_minimum_quotient
#print axioms LucasDescent.signed_attained
#print axioms LucasDescent.zero_label
#print axioms LucasDescent.signed_growth
#print axioms LucasDescent.least_residues

#print axioms LucasDescent.signed_iff
#print axioms LucasDescent.least_labels_odd
