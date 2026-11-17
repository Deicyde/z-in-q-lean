import OcticResidues
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas

namespace Sun28.OcticResidues

noncomputable section

theorem prime_divides_determinant {a b A B C D:ℤ} {p:ℕ} (pp:p.Prime)
    (ab:a.natAbs.Coprime b.natAbs) (h:(p:ℤ)∣A*a^2+B*b^2) (j:(p:ℤ)∣C*a^2+D*b^2) :
    (p:ℤ)∣A*D-B*C := by
  have ip:=Nat.prime_iff_prime_int.mp pp
  by_contra hn
  have aa:(p:ℤ)∣(A*D-B*C)*a^2:=by
    convert dvd_sub (dvd_mul_of_dvd_left h D) (dvd_mul_of_dvd_left j B) using 1;ring
  have bb:(p:ℤ)∣(A*D-B*C)*b^2:=by
    convert dvd_sub (dvd_mul_of_dvd_left j A) (dvd_mul_of_dvd_left h C) using 1;ring
  have pa:=ip.dvd_of_dvd_pow ((ip.dvd_mul.mp aa).resolve_left hn)
  have pb:=ip.dvd_of_dvd_pow ((ip.dvd_mul.mp bb).resolve_left hn)
  exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt
    (by simpa using Int.natAbs_dvd_natAbs.mpr pa)
    (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) ab

private theorem support_product {k N:ℕ} (sf:Squarefree k) (nz:N≠0)
    (h:∀ p:ℕ,p.Prime → p∣k → p∣N) : k∣N := by
  rw [←Nat.prod_primeFactors_of_squarefree sf,Nat.prod_primeFactors_dvd_iff nz]
  intro p hp
  have pp:=Nat.prime_of_mem_primeFactors hp
  exact Nat.mem_primeFactors.mpr ⟨pp,h _ pp (Nat.dvd_of_mem_primeFactors hp),nz⟩

private theorem both {a b:ℤ} {p:ℕ} (ab:a.natAbs.Coprime b.natAbs) (pp:p.Prime)
    (pa:(p:ℤ)∣a) (pb:(p:ℤ)∣b):False :=
  (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr pa)
    (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) ab

private theorem constant_hit {p N:ℕ} {z:ℤ} {k:ℕ} (pp:p.Prime) (mult:z.natAbs∣N^k)
    (pd:(p:ℤ)∣z) : p∣N :=
  pp.dvd_of_dvd_pow ((show p∣z.natAbs by simpa using Int.natAbs_dvd_natAbs.mpr pd).trans mult)

private theorem intersect_fg {a b:ℤ} {p:ℕ} (ab:a.natAbs.Coprime b.natAbs) (pp:p.Prime)
    (fa:(p:ℤ)∣f (a^2) (b^2)) (ga:(p:ℤ)∣g (a^2) (b^2)) : p∣7 := by
  have det:=prime_divides_determinant pp ab
    (A:=52822) (B:=(-1)) (C:=7203) (D:=109) (by simpa [f,sub_eq_add_neg] using fa) ga
  exact constant_hit (k:=8) pp (by decide) det

private theorem intersect_fh {a b:ℤ} {p:ℕ} (ab:a.natAbs.Coprime b.natAbs) (pp:p.Prime)
    (fa:(p:ℤ)∣f (a^2) (b^2)) (ha:(p:ℤ)∣h (a^2) (b^2)) : p∣154 := by
  let ip:=Nat.prime_iff_prime_int.mp pp
  have lift:(p:ℤ)∣(-348009506768)*a^4 := by
    convert dvd_sub ha (dvd_mul_of_dvd_left fa (6595547*a^2+109*b^2)) using 1; simp only [f,h]; ring
  rcases ip.dvd_mul.mp lift with pd|pa
  · exact constant_hit (k:=11) pp (by decide) pd
  · have pA:=ip.dvd_of_dvd_pow pa
    have t:(p:ℤ)∣b^2:=by
      convert dvd_sub (dvd_mul_of_dvd_right (dvd_pow pA (by decide:2≠0)) 52822) fa using 1; simp only [f]; ring
    exact (both ab pp pA (ip.dvd_of_dvd_pow t)).elim

private theorem intersect_gh {a b:ℤ} {p:ℕ} (ab:a.natAbs.Coprime b.natAbs) (pp:p.Prime)
    (ga:(p:ℤ)∣g (a^2) (b^2)) (ha:(p:ℤ)∣h (a^2) (b^2)) : p∣4578 := by
  let ip:=Nat.prime_iff_prime_int.mp pp
  have lift:(p:ℤ)∣5172686759688*b^4 := by
    convert dvd_sub (dvd_mul_of_dvd_right ha (7203^2))
      (dvd_mul_of_dvd_left ga (380476866*7203*a^2-47507725041*b^2)) using 1; simp only [g,h]; ring
  rcases ip.dvd_mul.mp lift with pd|pb
  · exact constant_hit (k:=11) pp (by decide) pd
  · have pB:=ip.dvd_of_dvd_pow pb
    have t:(p:ℤ)∣7203*a^2:=by
      convert dvd_sub ga (dvd_mul_of_dvd_right (dvd_pow pB (by decide:2≠0)) 109) using 1; simp only [g]; ring
    rcases ip.dvd_mul.mp t with pd|pa
    · exact constant_hit (k:=4) pp (by decide) pd
    · exact (both ab pp (ip.dvd_of_dvd_pow pa) pB).elim

private theorem signed_factor {F V Y:ℤ} {N:ℕ} (nz:F≠0) (n:N≠0) (seven:7∣N)
    (eqn:F*V=7*Y^2)
    (cover:∀p:ℕ,p.Prime → (p:ℤ)∣F → (p:ℤ)∣V → p∣N):
    ∃i U:ℤ, i.natAbs∣N ∧ F=i*U^2 := by
  obtain ⟨U,i,ui,si⟩:=exists_sq_mul_squarefree F
  have e:F=i*U^2:=by rw [←ui];ring
  have un:U≠0:=fun z=>nz (by rw [e,z];ring)
  have isq:IsSquare (((i*(7*V):ℤ):ℚ)):=by
    refine ⟨(7:ℚ)*Y/U,?_⟩
    have eq:((i:ℚ)*(U:ℚ)^2)*(V:ℚ)=7*(Y:ℚ)^2:=by exact_mod_cast e ▸ eqn
    push_cast
    field_simp [show (U:ℚ)≠0 by exact_mod_cast un]
    linear_combination eq
  obtain ⟨W,dw⟩:=Rat.isSquare_intCast_iff.mp isq
  have dv:i∣W^2:=by rw[sq,←dw];exact dvd_mul_right .. 
  obtain ⟨t,et⟩:=(si.dvd_pow_iff_dvd (by decide:2≠0)).mp dv
  have d:i∣7*V:=by
    refine ⟨t^2,?_⟩
    apply mul_left_cancel₀ si.ne_zero
    rw[dw,et];ring
  refine ⟨i,U,support_product (Int.squarefree_natAbs.mpr si) n ?_,e⟩
  intro p pp pk
  have z:(p:ℤ)∣i:=Int.natAbs_dvd_natAbs.mp (by simpa using pk)
  have hit:(p:ℤ)∣F:=e ▸ dvd_mul_of_dvd_left z _
  rcases (Nat.prime_iff_prime_int.mp pp).dvd_mul.mp (z.trans d) with se|oth
  · exact (show p∣7 by exact_mod_cast se).trans seven
  · exact cover p pp hit oth

theorem no_octic {a b Y:ℤ} (ab:a.natAbs.Coprime b.natAbs) (bn:b≠0) (yn:Y≠0)
    (eqn:f (a^2) (b^2)*g (a^2) (b^2)*h (a^2) (b^2)=7*Y^2) : False := by
  let F:=f (a^2) (b^2)
  let G:=g (a^2) (b^2)
  let H:=h (a^2) (b^2)
  have live:F*G*H≠0:=eqn ▸ mul_ne_zero (by decide) (pow_ne_zero 2 yn)
  have fn:F≠0:=fun e=>live (by rw[e];ring)
  have gp:0<G:=by dsimp [G,g];nlinarith only [sq_nonneg a,sq_pos_of_ne_zero bn]
  obtain ⟨i,U,ki,eu⟩:=signed_factor fn (by decide:154≠0) (by decide)
    (show F*(G*H)=7*Y^2 by linear_combination eqn) (by
      intro p pp fa hit
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_mul.mp hit with ga|ha
      · exact (intersect_fg ab pp fa ga).trans (by decide)
      · exact intersect_fh ab pp fa ha)
  obtain ⟨j,V,kj,ev⟩:=signed_factor gp.ne' (by decide:4578≠0) (by decide)
    (show G*(F*H)=7*Y^2 by linear_combination eqn) (by
      intro p pp ga hit
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_mul.mp hit with fa|ha
      · exact (intersect_fg ab pp fa ga).trans (by decide)
      · exact intersect_gh ab pp ga ha)
  have un:U≠0:=fun e=>fn (by rw[eu,e];ring)
  have vn:V≠0:=fun e=>gp.ne' (by rw[ev,e];ring)
  have jp:0<j:=by by_contra! le;exact (not_lt_of_ge (ev ▸ mul_nonpos_of_nonpos_of_nonneg le (sq_nonneg V))) gp
  have ex: IsSquare ((7*i*j*H:ℤ):ℚ):=by
    refine ⟨(7:ℚ)*Y/((U:ℚ)*V),?_⟩
    have equ:((i:ℚ)*(U:ℚ)^2)*((j:ℚ)*(V:ℚ)^2)*(H:ℚ)=7*(Y:ℚ)^2:=by
      exact_mod_cast (show (i*U^2)*(j*V^2)*H=7*Y^2 by rw [←eu,←ev];exact eqn)
    push_cast
    field_simp [show (U:ℚ)≠0 by exact_mod_cast un,show (V:ℚ)≠0 by exact_mod_cast vn]
    linear_combination equ
  obtain ⟨W,w⟩:=Rat.isSquare_intCast_iff.mp ex
  apply no_integral_cells (W:=W) ab _ eu ev (by simpa only [H,pow_two] using w)
  apply Finset.mem_product.mpr
  have ai:i.natAbs∈(154:ℕ).divisors:=Nat.mem_divisors.mpr ⟨ki,by decide⟩
  have bj:j.natAbs∈(4578:ℕ).divisors:=Nat.mem_divisors.mpr ⟨kj,by decide⟩
  refine ⟨?_,Finset.mem_image.mpr ⟨j.natAbs,bj,by simpa using abs_of_pos jp⟩⟩
  have vabs:(i.natAbs:ℤ)∈(154:ℕ).divisors.image (fun u:ℕ=>(u:ℤ)):=Finset.mem_image.mpr ⟨_,ai,rfl⟩
  by_cases ip : 0 ≤ i
  · exact Finset.mem_union_left _ (by simpa [abs_of_nonneg ip] using vabs)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i.natAbs:ℤ),vabs,by simp [abs_of_neg (lt_of_not_ge ip)]⟩)

end
end Sun28.OcticResidues
#print axioms Sun28.OcticResidues.no_octic
