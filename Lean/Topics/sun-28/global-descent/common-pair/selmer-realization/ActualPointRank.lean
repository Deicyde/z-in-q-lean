import SeededRealization
import ZInQKernel.Model.Field.ShortWeierstrass
import ZInQKernel.RouteK.Rank.Counting

namespace Sun28.SelmerRealization
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

/-- The four points killed by doubling on the actual twists, including infinity. -/
theorem four_torsion {l : ℕ} (lp : 0<l) :
    Nat.card (nsmulAddMonoidHom 2 : RationalPoint l →+ RationalPoint l).ker = 4 := by
  classical
  have ln : (0:ℚ)<l := by exact_mod_cast lp
  have regular (x : ℚ) (hx : x=0 ∨ x=l ∨ x= -3*l) : (twistCurve l).toAffine.Nonsingular x 0 := by
    rw [nonsingular_iff, equation_iff]
    rcases hx with h|h|h <;> subst x <;>
      simp [twistCurve,WeierstrassCurve.toAffine] <;> first | exact lp.ne' | (try constructor) <;> nlinarith [sq_pos_of_pos ln]
  let A : RationalPoint l := .some 0 0 (regular 0 (Or.inl rfl))
  let B : RationalPoint l := .some l 0 (regular _ (Or.inr (Or.inl rfl)))
  let C : RationalPoint l := .some (-3*l) 0 (regular _ (Or.inr (Or.inr rfl)))
  let φ : RationalPoint l →+ RationalPoint l := nsmulAddMonoidHom 2
  have eq : (φ.ker : Set (RationalPoint l))={0,A,B,C} := by
    ext P
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_insert_iff,Set.mem_singleton_iff]
    cases P with
    | zero => exact iff_of_true (map_zero φ) (Or.inl rfl)
    | @some x y h =>
      change 2 • Point.some x y h = 0 ↔ _
      rw [ZInQ.two_nsmul_some_eq_zero_iff]
      have negy : (twistCurve l).toAffine.negY x y= -y := by simp [negY,twistCurve,WeierstrassCurve.toAffine]
      rw [negy]
      simp only [Point.some_ne_zero, false_or, A,B,C, Point.some.injEq]
      constructor
      · intro yy
        obtain rfl : y=0 := by linarith
        have e := (equation_iff _ _).mp h.1
        simp [twistCurve,WeierstrassCurve.toAffine] at e
        have roots : x*(x-l)*(x+3*l)=0 := by linear_combination -e
        rcases mul_eq_zero.mp roots with w|w
        · rcases mul_eq_zero.mp w with w|w
          · exact Or.inl ⟨w,rfl⟩
          · exact Or.inr (Or.inl ⟨sub_eq_zero.mp w,rfl⟩)
        · exact Or.inr (Or.inr ⟨by linarith,rfl⟩)
      · rintro (⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩) <;> exact neg_zero.symm
  change Nat.card φ.ker=4
  rw [←SetLike.coe_sort_coe,eq,Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem,Set.ncard_insert_of_notMem,Set.ncard_pair]
  · simp [B,C,Point.some.injEq];linarith
  · simp [A,B,C,Point.some.injEq,ln.ne,ln.ne']
  · simp [A,B,C]

/-- Mordell--Weil finite generation and any point of infinite order give the
eight rational classes needed to exhaust the local two-Selmer group. -/
theorem eight_of_infinite_point {l : ℕ} (lp : 0<l) [AddGroup.FG (RationalPoint l)]
    (point : ∃ P : RationalPoint l, ¬ IsOfFinAddOrder P) : EightPointClasses l := by
  classical
  let A:=RationalPoint l
  let D := (nsmulAddMonoidHom 2 : A →+ A).range
  let : D.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (by decide : 2≠0)
  let : Fintype (A ⧸ D) := Fintype.ofFinite _
  have card := ZInQ.RouteK.Rank.eight_le_card_quotient_two (four_torsion lp) point
  change Nonempty (Fin 8 ↪ (A ⧸ D))
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using card

theorem prepared_scalar_of_infinite_point [AddGroup.FG (RationalPoint n)]
    (separates : KummerSeparation n) (finite : FiniteDescent n 526361 1)
    (point : ∃ P : RationalPoint n, ¬ IsOfFinAddOrder P) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  prepared_scalar_of_eight separates finite (eight_of_infinite_point (by decide) point)

end
end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.four_torsion
#print axioms Sun28.SelmerRealization.eight_of_infinite_point
#print axioms Sun28.SelmerRealization.prepared_scalar_of_infinite_point
