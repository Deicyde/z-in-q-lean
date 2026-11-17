import PrescribedReciprocity
import ReverseIndex
import ReverseClasses
import NewTwistPrimes
import SourceFacts

namespace Sun28.PrescribedPoints
open PairedClasses PreparedPoles TwistPrimes TwistExtension TwistRank ZInQ.RouteK
noncomputable section

/-- Fix the second squareclass first. The first class is an unbounded output. -/
theorem prescribed_second {θ : ℕ} (tp : 0<θ) (ts : Squarefree θ) (tm : θ%24=1) (B : ℕ) :
    ∃ b s h : ℕ,B<b ∧ θ<s^2 ∧ (s^2-θ)*(9*s^2-θ)=b*h^2 ∧ AdmissiblePair b θ ∧
      Family b θ ∧ TwistPoint b b ∧ TwistPoint b (b*θ) := by
  obtain ⟨p,large,sp⟩:=fresh_split tp B
  obtain ⟨s,lt,even,mod,co,simple⟩:=reverse_index tp tm sp
  let A:=(s^2-θ)*(9*s^2-θ)
  have nine : θ<9*s^2:=by omega
  have pos : 0<A:=Nat.mul_pos (Nat.sub_pos_of_lt lt) (Nat.sub_pos_of_lt nine)
  obtain ⟨h,_,eq⟩:=sqfNat_mul_sq pos.ne'
  let b:=sqfNat A
  change (s^2-θ)*(9*s^2-θ)=b*h^2 at eq
  have bs : Squarefree b:=sqfNat_squarefree A
  have nz : 0<b*h^2:=eq ▸ pos
  have bp : 0<b:=Nat.pos_of_ne_zero (fun z=>by simp [z] at nz)
  have hn : h≠0:=by rintro rfl;simp at nz
  have sn : s≠0:=by rintro rfl;simp at lt
  have integral : ((s:ℤ)^2-θ)*(9*(s:ℤ)^2-θ)=(b:ℤ)*h^2 := by
    have e:=congrArg (fun x : ℕ=>(x:ℤ)) eq
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub lt.le,Nat.cast_sub nine.le,Nat.cast_ofNat] using e
  have bh:= (forced_factor lt sp simple eq).1
  have row:=reverse_admissible tp ts tm co bp bs (reverse_residue tm even mod bs integral) integral
  have fam:=reciprocal_family bp (by exact_mod_cast sn : (s:ℚ)≠0) (by exact_mod_cast hn : (h:ℚ)≠0)
    (by exact_mod_cast integral)
  exact ⟨b,s,h,large.trans_le (Nat.le_of_dvd bp bh),lt,eq,row,fam,fixed_points_of_family bp tp fam⟩

theorem prescribed_second_with_norm {θ : ℕ} (big : 1<θ) (sf : Squarefree θ) (tm : θ%24=1)
    (B : ℕ) : ∃ b : ℕ,B<b ∧ AdmissiblePair b θ ∧ NormConic b θ ∧
      TwistPoint b b ∧ TwistPoint b (b*θ) := by
  obtain ⟨b,_,_,lb,_,_,adm,fam,pts⟩:=prescribed_second (by omega) sf tm B
  exact ⟨b,lb,adm,norm_conic adm.1 adm.2.1 sf big (family_norm fam),pts⟩
end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.prescribed_second
#print axioms Sun28.PrescribedPoints.prescribed_second_with_norm
