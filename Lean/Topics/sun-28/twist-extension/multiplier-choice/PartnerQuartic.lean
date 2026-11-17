import PoleTwistChoice

namespace Sun28.MultiplierChoice
open Sun28.Ordinary Sun28.ScalarHeight Sun28.PairedClasses Sun28.TwistExtension
noncomputable section

/-- The negative companion toggles the presence of the factor 3 in a listed multiplier. -/
def Partner (μ ν : ℚ) : Prop := ν = -3*μ ∨ 3*ν = -μ

theorem listed_partner {μ : ℚ} (member : μ∈smallMultipliers) :
    ∃ ν∈smallMultipliers, Partner μ ν := by
  obtain ⟨⟨g,a,b,i⟩,_,rfl⟩:=Finset.mem_image.mp member
  refine ⟨(shift (!g) a (!b) i:ℚ),Finset.mem_image.mpr ⟨(!g,a,!b,i),Finset.mem_univ _,rfl⟩,?_⟩
  cases b
  · left;cases g <;> cases a <;> simp [shift] <;> ring
  · right;cases g <;> cases a <;> simp [shift] <;> ring

theorem negative_of_partner {μ ν : ℚ} (mp:0<μ) (pair:Partner μ ν) : ν<0 := by
  rcases pair with rfl|h <;> linarith

/-- For either member of one signed pair, the common abscissa class is the
positive prepared class, and only the second twist ratio changes. -/
theorem two_branches_iff {μ ν B b a:ℚ} (bp:0<B) (short:B<μ) (bb:0<b) (an:a≠0)
    (A:μ*B=b*a^2) (comp:Partner μ ν) :
    ((∃e z,poleBranch μ B e z) ∨ (∃e z,poleBranch ν B e z)) ↔
      Surface b (1-B/μ) ∨ Surface b (1-B/ν) := by
  have mp : 0<μ:=bp.trans short
  have neg:=negative_of_partner mp comp
  have nonzero (w:ℚ) (wn:w≠0) (diff:B≠w) : 1-B/w≠0 := by
    intro e;apply diff;field_simp [wn] at e;linarith
  have tμ:=nonzero μ mp.ne' short.ne
  have diff : B≠ν:=ne_of_gt (neg.trans bp)
  have tν:=nonzero ν neg.ne diff
  have scale : ∃c:ℚ,c≠0 ∧ ν*B=(-3*b)*c^2 := by
    rcases comp with rfl|comp
    · exact ⟨a,an,by linear_combination -3*A⟩
    · exact ⟨a/3,div_ne_zero an (by norm_num),by linear_combination B/3*comp-A/3⟩
  obtain ⟨c,cn,E⟩:=scale
  rw [branch_iff_pair mp.ne' bp.ne' short.ne,branch_iff_pair neg.ne bp.ne' diff,A,E,
    pair_mark_scale an,pair_mark_scale cn,pair_marks bb.ne' tν]
  exact or_congr (surface_iff_pair bb tμ).symm (surface_iff_pair bb tν).symm

/-- A pointwise relation between the two different second twist ratios. Here
x=b(a/μ)²=B/μ. The alternative expression uses the reciprocal chart. -/
theorem product_quartic {μ ν B b a:ℚ} (mp:0<μ) (bp:0<B)
    (A:μ*B=b*a^2) (c:Partner μ ν) :
    (∃k:ℚ, k≠0 ∧ (1-B/μ)*(1-B/ν)=quartic b 1 k) ∨
    (∃k w:ℚ, k≠0 ∧ w≠0 ∧ -3*((1-B/μ)*(1-B/ν))=quartic b k 1*w^2) := by
  have nn:μ*B≠0:=(mul_pos mp bp).ne'
  have bn:b≠0:=left_ne_zero_of_mul (A ▸ nn)
  have an:a≠0:=fun z=>by subst a;simp only [zero_pow two_ne_zero,mul_zero] at A;exact nn A
  let x:=a/μ
  have xn:x≠0:=div_ne_zero an mp.ne'
  have r:B/μ=b*x^2:=by dsimp [x];field_simp [mp.ne'];linear_combination A
  rcases c with rfl|h
  · right
    refine ⟨b*x,1/b, mul_ne_zero bn xn,one_div_ne_zero bn,?_⟩
    have r₂:B/(-3*μ)=-(b*x^2)/3:=by rw [←r];ring
    rw [r₂,r]
    unfold quartic
    -- (b*x²−1)(b*x²+3) is F_b(b*x,1)/b².
    field_simp [bn];ring
  · left
    refine ⟨x,xn,?_⟩
    have eqν:ν= -μ/3:=by linarith
    have r₂:B/ν= -3*(b*x^2):=by rw [eqν,← r];ring
    rw [r₂,r];unfold quartic;ring
end
end Sun28.MultiplierChoice
#print axioms Sun28.MultiplierChoice.listed_partner
#print axioms Sun28.MultiplierChoice.negative_of_partner
#print axioms Sun28.MultiplierChoice.two_branches_iff
#print axioms Sun28.MultiplierChoice.product_quartic
