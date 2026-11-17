import TwistGroup

/-! From the two explicit Kummer coordinates to a rational point on the
corresponding two-cover. The exceptional points at x = 0, d, −d each use a
different zero square. -/
namespace ZInQBlueprint.Rank

noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

private theorem scaled (u a r : ℚ) (hu : IsSquare (u/a)) : IsSquare (u/(a*r^2)) := by
  obtain ⟨w,hw⟩ := hu
  refine ⟨w/r,?_⟩
  rw [div_mul_eq_div_div,hw]
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
  ring

private theorem cover_scale {d a b : ℚ} (r s : ℚ) (h : cover ℚ d a b) :
    cover ℚ d (a*r^2) (b*s^2) := by
  rcases h with ⟨⟨u,hu⟩,⟨v,hv⟩⟩ | ⟨x,hx,hm,hp⟩
  · left
    exact ⟨⟨u*r, by rw [hu]; ring⟩,⟨v*s, by rw [hv]; ring⟩⟩
  · right
    refine ⟨x,scaled _ _ r hx,scaled _ _ s hm,?_⟩
    have hfac : (a*r^2)*(b*s^2)=(a*b)*(r*s)^2 := by ring
    rw [hfac]
    exact scaled _ _ (r*s) hp

private theorem cover_coordinates (d : ℕ) (hd : 0 < d) (P : RationalPoint d) :
    cover ℚ d (kummer d P).1 (kummer d P).2 := by
  have hp : (0:ℚ)<d := by exact_mod_cast hd
  have hn : (d:ℚ) ≠ 0 := ne_of_gt hp
  rcases P with _ | @⟨x,y,h⟩
  · exact Or.inl ⟨⟨1,by norm_num [kummer]⟩,⟨1,by norm_num [kummer]⟩⟩
  · by_cases h₀ : x=0
    · subst x
      right
      refine ⟨0,⟨0,?_⟩,⟨1,?_⟩,⟨1,?_⟩⟩ <;> simp [kummer,hn]
    by_cases hpos : x=d
    · subst x
      right
      refine ⟨(d:ℚ),⟨1,?_⟩,⟨0,?_⟩,⟨1,?_⟩⟩ <;> simp [kummer,hn]
      field_simp
      ring
    by_cases hneg : x= -(d:ℚ)
    · subst x
      have hne : -(d:ℚ) ≠ d := by linarith
      right
      refine ⟨-(d:ℚ),⟨1,?_⟩,⟨1,?_⟩,⟨0,?_⟩⟩ <;> simp [kummer,hn,hne]
      field_simp
      ring
    right
    simp only [kummer,if_neg h₀,if_neg hpos,if_neg hneg]
    have hm : x-(d:ℚ) ≠ 0 := sub_ne_zero.mpr hpos
    refine ⟨x,⟨1,by simp [h₀]⟩,⟨1,by simp [hm]⟩,⟨y/(x*(x-d)),?_⟩⟩
    have e := h.1
    simp [equation_iff,congruentCurve] at e
    field_simp [h₀,hm]
    linear_combination -e

/-- A represented pair has a rational point on its explicit 2-cover. The
Selmer hypothesis is unnecessary for this implication. -/
theorem rationalCover_of_coordinates (d : ℕ) (hd : 0 < d) (P : RationalPoint d)
    (ab : ℤ × ℤ) (h : represents d P ab) : cover ℚ d ab.1 ab.2 := by
  obtain ⟨⟨r,_,hr⟩,⟨s,_,hs⟩⟩ := h
  rw [hr,hs]
  exact cover_scale r s (cover_coordinates d hd P)

theorem coverOfKummerCoordinates : CoverOfKummerCoordinates :=
  fun d hd P ab _ h => rationalCover_of_coordinates d hd P ab h

theorem allCoversOfCertifiedRow (d : ℕ) (hd : d % 8=5) (hs : Squarefree d)
    (comparison : DeterminantGenusComparison) (tyz : TYZGenusToAntiPoint)
    (eight : EightModTwoOfPositiveRank) (embedding : KummerEmbedding d)
    (hsize : (selmer d).ncard=8) (row : (smithM5b d).det=1) :
    ∀ ab ∈ selmer d, cover ℚ d ab.1 ab.2 :=
  allCoversOfGeometricRow d hd hs comparison tyz eight embedding coverOfKummerCoordinates hsize row

end
end ZInQBlueprint.Rank

#print axioms ZInQBlueprint.Rank.rationalCover_of_coordinates
#print axioms ZInQBlueprint.Rank.coverOfKummerCoordinates
#print axioms ZInQBlueprint.Rank.allCoversOfCertifiedRow
