import ConicSupport
import HomogeneousQuartics

namespace Sun28.ConicRemaining
open Sun28.ScalarRankZero Sun28.FactorHeights Sun28.OcticResidues
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

private def allowed (N:ℕ):Finset ℤ:=N.divisors.biUnion fun k=>{(k:ℤ),-(k:ℤ)}
private theorem mem_allowed (N:ℕ) (nz:N≠0) {m:ℤ} (hm:m.natAbs∣N) : m∈allowed N := by
  refine Finset.mem_biUnion.mpr ⟨m.natAbs,Nat.mem_divisors.mpr ⟨hm,nz⟩,?_⟩
  by_cases h : (0:ℤ) ≤ m
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

private theorem mod109 (m:ℤ) (hm:m∈allowed 9219) : IsSquare (m:ZMod 109) := by
  have list:allowed 9219=({-9219,-3073,-1317,-439,-21,-7,-3,-1,1,3,7,21,439,1317,3073,9219}:Finset ℤ) := by decide
  rw[list] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem special_line (a b z e t:ZMod 109) (h:z=a*t) (g:e*a+735*b=a*t^2) (r s:ZMod 109) :
    a*r^2-2*z*r*s+(e*a+735*b)*s^2=a*(r-t*s)^2 := by rw[h,g];ring

private theorem prime_cells {u v U V m:ℤ} {a b z e:ℤ} (cop:u.natAbs.Coprime v.natAbs)
    (at109:m∈allowed 9219) (hm:¬(109:ℤ)∣m)
    (na:¬IsSquare (a:ZMod 109)) (t:ZMod 109)
    (line:∀r s:ZMod 109, (a:ZMod 109)*r^2-2*(z:ZMod 109)*r*s+((e:ZMod 109)*(a:ZMod 109)+735*(b:ZMod 109))*s^2=(a:ZMod 109)*(r-t*s)^2)
    (ng:¬IsSquare ((b:ZMod 109)*(t^2-e)))
    (ef:m*(a*u^2-2*z*u*v+(e*a+735*b)*v^2)=U^2)
    (eg:m*(b*(u^2-e*v^2))=V^2) : False := by
  let : Fact (Nat.Prime 109):=⟨by decide⟩
  obtain ⟨k,hk⟩:=mod109 m at109
  have mn:(m:ZMod 109)≠0:=by exact fun h=>hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m 109).mp h)
  have kn:k≠0:=fun h=>mn (by rw[hk,h];ring)
  have f': (m:ZMod 109)*((a:ZMod 109)*((u:ZMod 109)-t*(v:ZMod 109))^2)=(U:ZMod 109)^2 := by
    rw[←line];simpa using congrArg (Int.castRingHom (ZMod 109)) ef
  have w:(u:ZMod 109)-t*(v:ZMod 109)=0:=by
    by_contra nw;apply na;refine ⟨(U:ZMod 109)/(k*((u:ZMod 109)-t*(v:ZMod 109))),?_⟩
    rw[hk] at f';field_simp [kn,nw];linear_combination f'
  have vn:(v:ZMod 109)≠0:=by
    intro vv;have uu:(u:ZMod 109)=0:=by simpa[vv] using w
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide:1<109)
      (by simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 109).mp uu))
      (by simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd v 109).mp vv))) cop
  have gg:(m:ZMod 109)*((b:ZMod 109)*((u:ZMod 109)^2-(e:ZMod 109)*(v:ZMod 109)^2))=(V:ZMod 109)^2:=by
    simpa using congrArg (Int.castRingHom (ZMod 109)) eg
  rw[hk,sub_eq_zero.mp w] at gg
  apply ng;refine ⟨(V:ZMod 109)/(k*(v:ZMod 109)),?_⟩;field_simp[kn,vn];linear_combination gg

private theorem even_cells : ∀m∈allowed 3073,∀u v:ZMod 16,
    ¬(ZMod.castHom (by decide:2∣16) (ZMod 2) u=0 ∧ ZMod.castHom (by decide:2∣16) (ZMod 2) v=0) →
    ¬((m:ZMod 16)*(-4*u^2-12*u*v+427*v^2)∈squares 16 ∧ (m:ZMod 16)*(u^2-77*v^2)∈squares 16) := by decide

/-- Every rational conic line in the three projective quartics is obstructed. -/
theorem empty_three : (¬represented 735 134288 2) ∧ (¬represented 735 134288 77) ∧ (¬represented 735 134288 154) := by
  have allj (j:Fin 3):¬represented 735 134288 (e₁ j) := by
    intro hp
    obtain ⟨u,v,cp,fn,joint⟩:=to_line j hp
    obtain ⟨m,U,V,hm,fu,gv⟩:=common_class j cp fn joint
    have dvd:m.natAbs∣9219:=hm.trans (by fin_cases j <;> decide : support₁ j∣9219)
    have h109:¬(109:ℤ)∣m:=fun h=>(by decide:¬109∣9219) ((show 109∣m.natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans dvd)
    have at109:=mem_allowed 9219 (by decide) dvd
    fin_cases j
    · apply prime_cells cp at109 h109 (a:=-57) (b:=7) (z:=1733) (e:=2) (by decide) 48 (special_line _ _ _ _ _ (by decide) (by decide)) (by decide) fu gv
    · have aa:=mem_allowed 3073 (by decide) hm
      have prim:¬(ZMod.castHom (by decide:2∣16) (ZMod 2) (u:ZMod 16)=0 ∧ ZMod.castHom (by decide:2∣16) (ZMod 2) (v:ZMod 16)=0) := by
        rintro ⟨hu,hv⟩;simp only [map_intCast] at hu hv
        exact (Nat.not_coprime_of_dvd_of_dvd (by decide:1<2)
          (by simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp hu))
          (by simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd v 2).mp hv))) cp
      apply even_cells m aa u v prim
      have mem (k:ℤ):(k:ZMod 16)^2∈squares 16 := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      constructor
      · convert mem U using 1
        simpa [f₁,a₁,b₁,z₁,e₁] using congrArg (Int.castRingHom (ZMod 16)) fu
      · convert mem V using 1
        simpa [g₁,b₁,e₁] using congrArg (Int.castRingHom (ZMod 16)) gv
    · apply prime_cells cp at109 h109 (a:=-8) (b:=3) (z:=8) (e:=154) (by decide) 108 (special_line _ _ _ _ _ (by decide) (by decide)) (by decide) fu gv
  exact ⟨allj 0,allj 1,allj 2⟩

end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.empty_three
