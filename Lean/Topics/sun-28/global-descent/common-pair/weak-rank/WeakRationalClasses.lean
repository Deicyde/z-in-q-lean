import WeakAbscissa

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.MarkedDescent Sun28.CompanionRank Sun28.GlobalSections ZInQ.Descent
noncomputable section

/-- Translation by an outside class doubles the four rational two-torsion classes. -/
theorem eight_abscissa {b k l : ℕ} (bb : 1<b) (kb : 1<k) (fac : l=b*k)
    (sf : Squarefree l) {P : RationalPoint l} (mark : rootClass l 0 P=sqc (b:ℚ)) :
    EightPointClasses l := by
  classical
  have bl : b<l := by rw [fac];nlinarith
  have lp : 0<l := by omega
  let T := (nsmulAddMonoidHom 2 : RationalPoint l →+ RationalPoint l).ker
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
      exact e
    obtain ⟨w,hw⟩ := QuotientAddGroup.eq_iff_sub_mem.mp zero
    apply AddSubgroup.mem_bot.mpr
    apply Subtype.ext
    exact two_double (by omega) sf t.property (by simpa only [sub_zero] using hw)
  let X : ModTwo l := QuotientAddGroup.mk P
  have outside (t : T) : X ≠ f t := outside_torsion bb kb fac sf mark t.property
  let g : T ⊕ T → ModTwo l := Sum.elim f (fun t => X+f t)
  have inj : Function.Injective g := by
    intro a b e
    cases a with
    | inl s =>
      cases b with
      | inl t => exact congrArg Sum.inl (fi e)
      | inr t =>
        change f s = X+f t at e
        exact False.elim (outside (s-t) (by rw [map_sub,e];abel))
    | inr s =>
      cases b with
      | inl t =>
        change X+f s=f t at e
        exact False.elim (outside (t-s) (by rw [map_sub,←e];abel))
      | inr t =>
        change X+f s=X+f t at e
        exact congrArg Sum.inr (fi (add_left_cancel e))
  have c : Fintype.card T=4 := by rwa [←Nat.card_eq_fintype_card]
  let e : Fin 8 ≃ (T⊕T) := Fintype.equivOfCardEq (by simp [c])
  exact ⟨e.toEmbedding.trans ⟨g,inj⟩⟩

theorem candidate_strict {b d q : ℕ} (ad : Sun28.PairedClasses.AdmissiblePair b d)
    (C : Sun28.SeededPartners.Candidate b d q) (hit : strictPoint b ((b*q)*d)) :
    (∃ P : RationalPoint ((b*q)*d), rootClass ((b*q)*d) 0 P=sqc (b:ℚ) ∧ ¬IsOfFinAddOrder P) ∧
    EightPointClasses ((b*q)*d) := by
  have cop := C.coprime.coprime_dvd_right (dvd_mul_left d 6)
  have sf := Nat.squarefree_mul_iff.mpr ⟨cop,C.squarefree,ad.2.2.2.1⟩
  have r := ad.2.2.2.2.2.2.2.1
  have b1 : 1<b := by omega
  have dp := ad.2.1
  have qp := C.nontrivial
  have qd : 1<q*d := by nlinarith
  have h := strict_point_rank b1 qd (Nat.mul_assoc b q d) sf hit
  obtain ⟨P,mark,non⟩ := h
  exact ⟨⟨P,mark,non⟩,eight_abscissa b1 qd (Nat.mul_assoc b q d) sf mark⟩

theorem rational_eight {l : ℕ} (lp : 0<l) (eight : EightPointClasses l) :
    ∃ f : Fin 8 → ℤ × ℤ, Function.Injective f ∧ ∀ i, f i∈localClasses l ∧ Cover ℚ l (f i).1 (f i).2 := by
  classical
  obtain ⟨j⟩ := eight
  choose rep eq_rep using (fun i : Fin 8 => QuotientAddGroup.mk_surjective (j i))
  refine ⟨fun i => labels l (rep i),?_,fun i => ⟨labels_local lp _,labels_cover lp _⟩⟩
  intro i i' eq
  exact j.injective ((eq_rep i).symm.trans ((kummer_separation lp _ _ eq).trans (eq_rep i')))

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.eight_abscissa
#print axioms Sun28.WeakRank.candidate_strict
#print axioms Sun28.WeakRank.rational_eight
