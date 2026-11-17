import SingleSection
import TorsionMarksPair

/-! A failure of the single-quartic test excludes all four marked point sections on the two fixed twists. -/
namespace Sun28.CommonPair
open Sun28.PrescribedPoints Sun28.PairedClasses Sun28.TwistExtension Sun28.GlobalDescent Sun28.PointFibres
noncomputable section

theorem one_four_marks {b d:ℚ} (bp:0<b) (dp:0<d) (bs:¬IsSquare b) (ds:¬IsSquare d) :
    OneQuartic b d ↔
      Point b (b*d) ∨ Point b ((-3*b)*d) ∨ Point d (b*d) ∨ Point d ((-3*b)*d) := by
  have a:=one_quartic_iff (b:=b) bp dp.ne'
  have c:=one_quartic_iff (b:=d) dp bp.ne'
  have sw:=one_symmetry bp dp bs ds
  rw [mul_comm d b,show (-3*d)*b=(-3*b)*d by ring] at c
  constructor
  · intro h;rcases a.mp h with pos|neg
    · exact Or.inl pos
    · exact Or.inr (Or.inl neg)
  · rintro (p|p|p|p)
    · exact a.mpr (Or.inl p)
    · exact a.mpr (Or.inr p)
    · exact sw.mpr (c.mpr (Or.inl p))
    · exact sw.mpr (c.mpr (Or.inr p))

/-- For the fixed independently prepared scalar data, failure of all four stationary
marked classes forces a genuinely moving simultaneous pair on any feasible surface. -/
theorem fixed_surface_iff :
    Surface 526361 526681 ↔
      Point 526361 277224337841 ∨ Point 526361 (-831673013523) ∨
      Point 526681 277224337841 ∨ Point 526681 (-831673013523) ∨
      NonzeroPair 526361 526681 := by
  rw [surface_iff_one_or_nonzero (by norm_num) (by norm_num)]
  have z:=one_four_marks (b:=526361) (d:=526681) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num1 at z
  rw [z]
  tauto

end
end Sun28.CommonPair
#print axioms Sun28.CommonPair.one_four_marks
#print axioms Sun28.CommonPair.fixed_surface_iff
