import PublicAssembly
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.Finiteness

/-! Classical inputs to full two-descent on the congruent-number curves. -/
namespace ZInQBlueprint.Rank

noncomputable section
attribute [local instance] Classical.decEq

/-- Mordell, *On the rational solutions of the indeterminate equations of the
third and fourth degrees* (1922), pp. 179–180, specialized to C_d over Q. -/
def MordellFiniteGeneration : Prop :=
  ∀ d : ℕ, 0 < d → AddGroup.FG (RationalPoint d)

/-- Milne, *Elliptic Curves* (2006), IV §3, Remark 3.7, p. 113, referring
to Cassels, *Lectures on Elliptic Curves*, Chapter 15. Equality of the two
explicit squareclasses detects equality of classes modulo doubles. -/
def FullTwoDescent (d : ℕ) : Prop :=
  ∀ P Q : RationalPoint d, (QuotientAddGroup.mk P : modTwo d) = QuotientAddGroup.mk Q ↔
    sameSquareclass (kummer d P).1 (kummer d Q).1 ∧
    sameSquareclass (kummer d P).2 (kummer d Q).2

private lemma class_trans {a b c : ℚ} (h : sameSquareclass a b)
    (g : sameSquareclass b c) : sameSquareclass a c := by
  obtain ⟨r,hr,er⟩ := h
  obtain ⟨s,hs,es⟩ := g
  exact ⟨r*s,mul_ne_zero hr hs,by rw [er,es]; ring⟩

private lemma class_symm {a b : ℚ} (h : sameSquareclass a b) : sameSquareclass b a := by
  obtain ⟨r,hr,er⟩ := h
  refine ⟨r⁻¹,inv_ne_zero hr,?_⟩
  rw [er]
  field_simp

/-- Every nonzero rational squareclass contains a signed squarefree integer. -/
theorem signed_squarefree_representative (q : ℚ) (hq : q ≠ 0) :
    ∃ a : ℤ, Squarefree a ∧ sameSquareclass (a:ℚ) q := by
  let z : ℤ := q.num*(q.den:ℤ)
  have hz : z ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_ne_zero)
  obtain ⟨s,b,_,hb,eqn,hs⟩ := Nat.sq_mul_squarefree_of_pos (n:=z.natAbs) (by omega)
  let a : ℤ := if 0 ≤ z then (s:ℤ) else -(s:ℤ)
  have ha : Squarefree a := by
    apply Int.squarefree_natAbs.mp
    simpa [a,apply_ite Int.natAbs] using hs
  have hz' : (b:ℤ)^2*(s:ℤ) = |z| := by
    simpa only [Nat.cast_natAbs] using (show (b:ℤ)^2*(s:ℤ) = (z.natAbs:ℤ) by exact_mod_cast eqn)
  have hzrep : (b:ℤ)^2*a = z := by
    dsimp [a]
    split_ifs with pos
    · rwa [abs_of_nonneg pos] at hz'
    · rw [abs_of_neg (by omega : z < 0)] at hz'
      linarith only [hz']
  have rat_eq : (b:ℚ)^2*(a:ℚ) = (q.num:ℚ)*(q.den:ℚ) := by exact_mod_cast hzrep
  have bq : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have dq : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  refine ⟨a,ha,(q.den:ℚ)/b,div_ne_zero dq bq,?_⟩
  have qeq : q = (q.num:ℚ)/(q.den:ℚ) := q.num_div_den.symm
  calc
    (a:ℚ) = ((q.num:ℚ)/(q.den:ℚ))*((q.den:ℚ)/b)^2 := by
      field_simp [bq,dq]
      linarith only [rat_eq]
    _ = q*((q.den:ℚ)/b)^2 := by rw [← qeq]

private theorem kummer_ne_zero (d : ℕ) (hd : 0 < d) (P : RationalPoint d) :
    (kummer d P).1 ≠ 0 ∧ (kummer d P).2 ≠ 0 := by
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  cases P with
  | zero => simp [kummer]
  | @some x y h =>
    by_cases hz : x=0
    · simp [kummer,hz,hdq]
    by_cases hp : x=d
    · simp [kummer,hp,hdq]
    by_cases hm : x= -(d:ℚ)
    · simp [kummer,hm,hdq,hd.ne']
    · simp [kummer,hz,hp,hm,sub_ne_zero.mpr hp]

private theorem class_in_selmer (d : ℕ) (hd : 0 < d) (P : RationalPoint d) :
    ∃ ab : ℤ × ℤ, ab ∈ selmer d ∧ represents d P ab := by
  obtain ⟨ha,hb⟩ := kummer_ne_zero d hd P
  obtain ⟨a,fa,ea⟩ := signed_squarefree_representative _ ha
  obtain ⟨b,fb,eb⟩ := signed_squarefree_representative _ hb
  have represented : represents d P (a,b) := ⟨ea,eb⟩
  exact ⟨(a,b), ZInQBlueprint.Descent.mem_of_rational fa fb
    (rationalCover_of_coordinates d hd P (a,b) represented), represented⟩

/-- Choose one point in each coset and normalize its two coordinates. The
kernel criterion proves both injectivity and compatibility with every other
representative of that coset. -/
noncomputable def kummerEmbedding_of_fullTwoDescent (d : ℕ) (hd : 0 < d)
    (descent : FullTwoDescent d) : KummerEmbedding d := by
  let repr (c : modTwo d) : RationalPoint d := (QuotientAddGroup.mk_surjective c).choose
  have eq_repr (c : modTwo d) : QuotientAddGroup.mk (repr c) = c := (QuotientAddGroup.mk_surjective c).choose_spec
  let pair (c : modTwo d) : ℤ × ℤ := (class_in_selmer d hd (repr c)).choose
  have member (c : modTwo d) : pair c ∈ selmer d := (class_in_selmer d hd (repr c)).choose_spec.1
  have represented (c : modTwo d) : represents d (repr c) (pair c) := (class_in_selmer d hd (repr c)).choose_spec.2
  refine ⟨⟨fun c => ⟨pair c,member c⟩,?_⟩,?_⟩
  · intro c e he
    have eqp : pair c = pair e := congrArg Subtype.val he
    have hc := represented c
    rw [eqp] at hc
    have he' := represented e
    calc
      c = QuotientAddGroup.mk (repr c) := (eq_repr c).symm
      _ = QuotientAddGroup.mk (repr e) := (descent _ _).mpr
        ⟨class_trans (class_symm hc.1) he'.1, class_trans (class_symm hc.2) he'.2⟩
      _ = e := eq_repr e
  · intro P
    let c : modTwo d := QuotientAddGroup.mk P
    have eqc := (descent (repr c) P).mp (eq_repr c)
    exact ⟨class_trans (represented c).1 eqc.1, class_trans (represented c).2 eqc.2⟩

/-- Use scalar normalization and the classical two-descent criterion in the
public row-5b argument. The finite quotient count is a separate input. -/
theorem public_rank_of_fullTwoDescent
    (row : ZInQBlueprint.PublicText.MatrixTest) (genus : DeterminantGenusComparison)
    (point : TYZGenusToAntiPoint) (eight : EightModTwoOfPositiveRank)
    (descent : ∀ d : ℕ, d % 8 = 5 → Squarefree d → FullTwoDescent d) :
    ZInQBlueprint.PublicText.CertifiedRankSel :=
  ZInQBlueprint.PublicText.rank_of_four row genus point eight
    (fun d hd hs => kummerEmbedding_of_fullTwoDescent d (by omega) (descent d hd hs))

#print axioms public_rank_of_fullTwoDescent
#print axioms signed_squarefree_representative
#print axioms kummerEmbedding_of_fullTwoDescent
end
end ZInQBlueprint.Rank
