import TorsionLabels

namespace Sun28.CompanionRank
open Sun28.SelmerRealization Sun28.MarkedDescent ZInQ.RouteK
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

private theorem nonsquare {m : ℕ} (sf : Squarefree m) (h : 1 < m) : ¬IsSquare (m:ℚ) := by
  intro H
  obtain ⟨z,e⟩ := Rat.isSquare_natCast_iff.mp H
  rw [e] at sf h
  have unit := sf z dvd_rfl
  rw [Nat.isUnit_iff] at unit
  simp [unit] at h

/-- A rational point on the marked projective cover yields a rational
elliptic point carrying exactly the ordered label (b,1). -/
theorem point_of_cover {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) (M : Cover ℚ l b 1) :
    ∃ P : RationalPoint l, labels l P=((b:ℤ),1) := by
  have pos : 0<(b:ℚ) := by exact_mod_cast (show 0<b by omega)
  have kpos : 0<k := by omega
  have lp : 0<l := fac ▸ (Nat.mul_pos (by omega) kpos)
  have ln : 0<(l:ℚ) := by exact_mod_cast lp
  obtain ⟨_,sB,sK⟩ := Nat.squarefree_mul_iff.mp (fac ▸ sf)
  have quot : (l:ℚ)/b=k := by rw [fac,Nat.cast_mul,mul_div_cancel_left₀ _ pos.ne']
  have m : Sun28.SupportMatrix.MarkedCover (b:ℚ) (l:ℚ) := by simpa using (rational_cover l b).mp M
  obtain ⟨u,v,w,un,vn,wn,h1,h2⟩ := Sun28.SupportMatrix.cover_affine pos ln
    (nonsquare sB bb) (quot ▸ nonsquare sK kb) m
  let x : ℚ := b*u^2
  let y : ℚ := b*u*v*w
  have yy : y≠0 := by dsimp [y]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero pos.ne' un) vn) wn
  have xx : x≠0 := by dsimp [x];exact mul_ne_zero pos.ne' (pow_ne_zero _ un)
  have xu : x≠(l:ℚ) := by
    intro h
    change x-l=v^2 at h1
    rw [h,sub_self] at h1
    exact vn (by nlinarith)
  have xv : x≠ -3*(l:ℚ) := by
    have : 0 ≤ x := mul_nonneg pos.le (sq_nonneg u)
    linarith
  have eq : y^2=x*(x-l)*(x+3*l) := by
    change x-l=v^2 at h1
    change x+3*l=(b:ℚ)*w^2 at h2
    rw [h1,h2]
    dsimp [x,y]
    ring
  have ns : (twistCurve l).toAffine.Nonsingular x y := by
    rw [nonsingular_iff]
    refine ⟨equation.mpr eq, Or.inr ?_⟩
    simp only [twistCurve, WeierstrassCurve.toAffine,zero_mul,sub_zero]
    exact fun h => yy (by linarith)
  refine ⟨.some x y ns,?_⟩
  change (sqf _,sqf _) = ((b:ℤ),1)
  simp only [raw,ite_eq_right xx,ite_eq_right xu,ite_eq_right xv]
  exact Prod.ext (sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sB) wn
    (by simpa only [Int.cast_natCast] using h2))
    (sqf_eq_of_eq_mul_sq (d:=1) squarefree_one vn (by simpa only [Int.cast_one,one_mul] using h1))

/-- Translation by an outside point doubles the four classes of rational
two-torsion. This argument is valid without finite generation. -/
theorem eight_of_label {b l : ℕ} (bb : 1<b) (bl : b<l) (sf : Squarefree l)
    {P : RationalPoint l} (mark : labels l P=((b:ℤ),1)) : EightPointClasses l := by
  classical
  let T := (nsmulAddMonoidHom 2 : RationalPoint l →+ RationalPoint l).ker
  have lp : 0<l := by omega
  have big : 1<l := by omega
  have card : Nat.card T=4 := four_torsion lp
  let : Finite T := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype T := Fintype.ofFinite T
  let f : T →+ ModTwo l := (QuotientAddGroup.mk' (doubles (RationalPoint l))).comp T.subtype
  have fi : Function.Injective f := by
    apply (AddMonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro t e
    have zero : (QuotientAddGroup.mk t.val : ModTwo l) = QuotientAddGroup.mk (0 : RationalPoint l) := by
      rw [QuotientAddGroup.mk_zero]
      change f t=0
      exact e
    obtain ⟨w,hw⟩ := QuotientAddGroup.eq_iff_sub_mem.mp zero
    apply AddSubgroup.mem_bot.mpr
    apply Subtype.ext
    exact two_double big sf t.property (by simpa only [sub_zero] using hw)
  let X : ModTwo l := QuotientAddGroup.mk P
  have outside (t : T) : X ≠ f t := by
    intro copy
    have lab := (Sun28.Corank.quotient_label lp (show (QuotientAddGroup.mk P : ModTwo l)=QuotientAddGroup.mk t.val from copy)).symm.trans mark
    rcases two_label lp sf t.property with ht|neg|number
    · rw [ht,label_zero] at lab
      have e : (1:ℤ)=b := congrArg Prod.fst lab
      omega
    · rw [lab] at neg;norm_num at neg
    · have e : (l:ℤ)=b := congrArg Prod.fst (number.symm.trans lab)
      omega
  let g : T ⊕ T → ModTwo l := Sum.elim f (fun t => X+f t)
  have inj : Function.Injective g := by
    intro a b e
    cases a with
    | inl s =>
      cases b with
      | inl t => exact congrArg Sum.inl (fi e)
      | inr t =>
        change f s = X+f t at e
        exact False.elim (outside (s-t) (by rw [map_sub,e]; abel))
    | inr s =>
      cases b with
      | inl t =>
        change X+f s=f t at e
        exact False.elim (outside (t-s) (by rw [map_sub,←e]; abel))
      | inr t =>
        change X+f s=X+f t at e
        exact congrArg Sum.inr (fi (add_left_cancel e))
  have c : Fintype.card T=4 := by rwa [←Nat.card_eq_fintype_card]
  let e : Fin 8 ≃ (T⊕T) := Fintype.equivOfCardEq (by simp [c])
  exact ⟨e.toEmbedding.trans ⟨g,inj⟩⟩

theorem marked_cover_rank {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) (M : Cover ℚ l b 1) :
    (∃ P : RationalPoint l, labels l P=((b:ℤ),1) ∧ ¬IsOfFinAddOrder P) ∧ EightPointClasses l := by
  obtain ⟨P,mark⟩ := point_of_cover bb kb fac sf M
  have bl : b<l := by rw [fac]; nlinarith
  exact ⟨⟨P,mark,marked_label_infinite bb bl sf mark⟩,eight_of_label bb bl sf mark⟩

end
end Sun28.CompanionRank

#print axioms Sun28.CompanionRank.point_of_cover
#print axioms Sun28.CompanionRank.eight_of_label
#print axioms Sun28.CompanionRank.marked_cover_rank
