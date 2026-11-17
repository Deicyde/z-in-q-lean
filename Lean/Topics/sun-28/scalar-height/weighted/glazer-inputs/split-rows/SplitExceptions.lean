import SplitRows
import OriginalRows

/-! Apply the three-point arc estimate to the original five-mark heights. -/
namespace ZInQBlueprint.SplitRows
open Finset Sun28.Ordinary ZInQBlueprint.OriginalHeightCount
open scoped Classical
attribute [local irreducible] glazerConstant24
set_option maxRecDepth 12000
noncomputable section

theorem record_of_rows {x : ℚ} {B K da db dc u v w : ℕ}
    (boundA : x.num.natAbs ≤ B) (boundB : x.den ≤ B)
    (Anon : x.num≠0) (Cnon : x.num-(x.den:ℤ)≠0)
    (ap : 0 < da) (bp : 0 < db) (cp : 0 < dc)
    (ak : da≤K) (bk : db≤K) (ck : dc≤K)
    (A : x.num.natAbs=da*u^2) (Bval : x.den=db*v^2) (C : (x.num-(x.den:ℤ)).natAbs=dc*w^2) :
    ∃ s : Record x B K, s.i*s.j*s.k=da*db*dc := by
  have aval : 0 < da*u^2 := by rw [←A];exact Int.natAbs_pos.mpr Anon
  have bval : 0 < db*v^2 := by rw [←Bval];exact x.den_pos
  have cval : 0 < dc*w^2 := by rw [←C];exact Int.natAbs_pos.mpr Cnon
  have dbn : (x.den:ℝ)≠0 := by exact_mod_cast x.den_nz
  have xr : (x:ℝ)=(x.num:ℝ)/(x.den:ℝ) := by exact_mod_cast x.num_div_den.symm
  by_cases neg : x.num<0
  · have chamber : ray x=.negative := by unfold ray; grind only
    have aabs : (x.num.natAbs:ℤ) = -x.num := (Int.natCast_natAbs _).trans (abs_of_neg neg)
    have cabs : ((x.num-(x.den:ℤ)).natAbs:ℤ) = (x.den:ℤ)-x.num := by
      rw [Int.natCast_natAbs,abs_of_neg (by omega)];ring
    have add : x.num.natAbs+x.den=(x.num-(x.den:ℤ)).natAbs := by omega
    have rn : (x.num:ℝ)-(x.den:ℝ)≠0 := by exact_mod_cast Cnon
    refine ⟨⟨da,db,dc,⟨u,v,w⟩,⟨aval,bval,by dsimp;rw [←A,←Bval,←C];exact add⟩,
      ap,bp,cp,ak,bk,ck,by dsimp;rw [←C,←add];omega,?_⟩,rfl⟩
    change value (ray x) (x:ℝ) = ((da*u^2:ℕ):ℝ)/((dc*w^2:ℕ):ℝ)
    rw [chamber,←A,←C]
    change (x:ℝ)/((x:ℝ)-1)=_
    have av : (x.num.natAbs:ℝ)= -(x.num:ℝ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z:ℤ=>(z:ℝ)) aabs
    have cv : ((x.num-(x.den:ℤ)).natAbs:ℝ)=(x.den:ℝ)-(x.num:ℝ) := by simpa only [Int.cast_natCast,Int.cast_sub] using congrArg (fun z:ℤ=>(z:ℝ)) cabs
    rw [xr,av,cv];field_simp [dbn,rn,show (x.den:ℝ)-(x.num:ℝ)≠0 from sub_ne_zero.mpr (sub_ne_zero.mp rn).symm];ring
  · have aabs : (x.num.natAbs:ℤ)=x.num := (Int.natCast_natAbs _).trans (abs_of_nonneg (le_of_not_gt neg))
    have av : (x.num.natAbs:ℝ)=(x.num:ℝ) := by simpa only [Int.cast_natCast] using congrArg (fun z:ℤ=>(z:ℝ)) aabs
    by_cases mid : x.num<(x.den:ℤ)
    · have chamber : ray x=.middle := by unfold ray; grind only
      have cabs : ((x.num-(x.den:ℤ)).natAbs:ℤ)=(x.den:ℤ)-x.num := by
        rw [Int.natCast_natAbs,abs_of_neg (by omega)];ring
      have add : x.num.natAbs+(x.num-(x.den:ℤ)).natAbs=x.den := by omega
      refine ⟨⟨da,dc,db,⟨u,w,v⟩,⟨aval,cval,by dsimp;rw [←A,←Bval,←C];exact add⟩,
        ap,cp,bp,ak,ck,bk,by dsimp; rw [←Bval];omega,?_⟩,by dsimp;ring⟩
      change value (ray x) (x:ℝ) = ((da*u^2:ℕ):ℝ)/((db*v^2:ℕ):ℝ)
      rw [chamber,←A,←Bval,av]
      exact xr
    · have chamber : ray x=.upper := by unfold ray; grind only
      have cabs : ((x.num-(x.den:ℤ)).natAbs:ℤ)=x.num-(x.den:ℤ) :=
        (Int.natCast_natAbs _).trans (abs_of_nonneg (by omega))
      have add : x.den+(x.num-(x.den:ℤ)).natAbs=x.num.natAbs := by omega
      refine ⟨⟨db,dc,da,⟨v,w,u⟩,⟨bval,cval,by dsimp;rw [←A,←Bval,←C];exact add⟩,
        bp,cp,ap,bk,ck,ak,by dsimp; rw [←A];omega,?_⟩,by dsimp;ring⟩
      change value (ray x) (x:ℝ) = ((db*v^2:ℕ):ℝ)/((da*u^2:ℕ):ℝ)
      rw [chamber,←A,←Bval,av]
      change (x:ℝ)⁻¹=_
      rw [xr,inv_div]


theorem record_at_failure {x : ℚ} {B K : ℕ} (hx : x∈exceptions B)
    (lim : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) : Nonempty (Record x B K) := by
  obtain ⟨box,off,_⟩:=(mem_exceptions x B).mp hx
  obtain ⟨da,u,ap,ak,ea⟩:=row_square_at_failure hx lim 1
  obtain ⟨db,v,bp,bk,eb⟩:=row_square_at_failure hx lim 0
  obtain ⟨dc,w,cp,ck,ec⟩:=row_square_at_failure hx lim 2
  have eqB : x.den=db*v^2 := by exact eb
  obtain ⟨s,_⟩:=record_of_rows (max_le_iff.mp box).1 (max_le_iff.mp box).2 (off 1) (off 2)
    ap bp cp ak bk ck ea eqB ec
  exact ⟨s⟩

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.record_of_rows
#print axioms ZInQBlueprint.SplitRows.record_at_failure
