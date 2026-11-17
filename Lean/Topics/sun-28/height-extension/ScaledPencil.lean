import FinitePell

/-! Remove the square part of the selected row by working over its actual
finite primes. The three resulting rational variables have controlled denominators. -/
namespace Sun28.HeightExtension
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK
open private leftRow midRow rightRow mult catalogue delta₁ delta₂ linear_log equation_rows from FivePencils
noncomputable section

def rowPrimes (i : Fin 5) (A B : ℤ) := (oldForm i A B).natAbs.primeFactors

private theorem denom_le {a b F : ℤ} (_bn:b≠0) (fn:F≠0) (div:b∣F) :
    (((a:ℚ)/(b:ℚ)).den).primeFactors⊆F.natAbs.primeFactors := by
  have rel : ((((a:ℚ)/(b:ℚ)).den:ℕ):ℤ)∣b:=by
    simpa only [←Rat.divInt_eq_div] using Rat.den_dvd a b
  have dv : ((a:ℚ)/(b:ℚ)).den ∣ F.natAbs:=Int.natAbs_dvd_natAbs.mpr (rel.trans div)
  exact Nat.primeFactors_mono dv (Int.natAbs_ne_zero.mpr fn)

/-- Three rationals with the same explicit denominator repack the two equations.
The remaining right sides are the signed squarefree part of the selected row,
multiplied by fixed determinants. -/
theorem rational_pencil {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) :
    ∃ (g h k I J : ℤ) (x y z : ℚ),
      g≠0 ∧ h≠0 ∧ k≠0 ∧ I≠0 ∧ J≠0 ∧ I≠J ∧
      g.natAbs.primeFactors⊆support A B ∧ h.natAbs.primeFactors⊆support A B ∧ k.natAbs.primeFactors⊆support A B ∧
      (∀ c∈([g,h,k,I,J]:List ℤ),c.natAbs≤2^32*heightRadical A B) ∧
      x.den.primeFactors⊆rowPrimes i A B ∧ y.den.primeFactors⊆rowPrimes i A B ∧ z.den.primeFactors⊆rowPrimes i A B ∧
      (g:ℚ)*x^2-(h:ℚ)*y^2=(I:ℚ) ∧ (g:ℚ)*x^2-(k:ℚ)*z^2=(J:ℚ) ∧
      (oldForm (leftRow i) A B:ℚ)/(oldForm i A B:ℚ)=
        (kernel (leftRow i) A B:ℚ)/(kernel i A B:ℚ)*x^2 := by
  let l:=leftRow i;let m:=midRow i;let n:=rightRow i
  obtain ⟨_,a,_,fa⟩:=sqfInt_spec (off l)
  obtain ⟨_,b,_,fb⟩:=sqfInt_spec (off m)
  obtain ⟨_,c,_,fc⟩:=sqfInt_spec (off n)
  obtain ⟨_,v,nv,fv⟩:=sqfInt_spec (off i)
  change oldForm l A B=kernel l A B*a^2 at fa
  change oldForm m A B=kernel m A B*b^2 at fb
  change oldForm n A B=kernel n A B*c^2 at fc
  change oldForm i A B=kernel i A B*v^2 at fv
  obtain ⟨mu,nd,ne,de,bd,be⟩:=catalogue i
  have nz (r : Fin 5):kernel r A B≠0 := (sqfInt_spec (off r)).1.ne_zero
  let G (j:Fin 3) (r:Fin 5):=mult i j*kernel r A B
  have live (j r) : G j r≠0:=mul_ne_zero (mu j).1 (nz r)
  have cap {d:ℤ} (hd:d.natAbs≤2^32) (r:Fin 5) :
      (d*kernel r A B).natAbs≤2^32*heightRadical A B := by
    rw [Int.natAbs_mul];exact Nat.mul_le_mul hd (kernel_bound off r)
  have vd : v ∣ oldForm i A B := by rw [fv];exact ⟨kernel i A B*v,by ring⟩
  have ps (a:ℤ) : (((a:ℚ)/(v:ℚ)).den).primeFactors⊆rowPrimes i A B:=denom_le nv (off i) vd
  obtain ⟨e₁,e₂⟩:=equation_rows i A B
  change mult i 0*oldForm l A B-mult i 1*oldForm m A B=delta₁ i*oldForm i A B at e₁
  change mult i 0*oldForm l A B-mult i 2*oldForm n A B=delta₂ i*oldForm i A B at e₂
  rw [fa,fb,fv] at e₁;rw [fa,fc,fv] at e₂
  have qnv:(v:ℚ)≠0:=by exact_mod_cast nv
  have cast₁:=congrArg (fun u:ℤ=>(u:ℚ)) e₁
  have cast₂:=congrArg (fun u:ℤ=>(u:ℚ)) e₂
  push_cast at cast₁ cast₂
  refine ⟨G 0 l,G 1 m,G 2 n,delta₁ i*kernel i A B,delta₂ i*kernel i A B,
    (a:ℚ)/v,(b:ℚ)/v,(c:ℚ)/v,live 0 l,live 1 m,live 2 n,mul_ne_zero nd (nz i),
    mul_ne_zero ne (nz i),fun e=>de (mul_right_cancel₀ (nz i) e),
    scaled_support off i 0 l,scaled_support off i 1 m,scaled_support off i 2 n,?_,
    ps a,ps b,ps c,?_,?_,?_⟩
  · intro w hw;simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl
    exacts [cap (mu 0).2 l,cap (mu 1).2 m,cap (mu 2).2 n,cap bd i,cap be i]
  · dsimp [G];push_cast;field_simp;linear_combination cast₁
  · dsimp [G];push_cast;field_simp;linear_combination cast₂
  · rw [fa,fv];push_cast;ring

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.rational_pencil
