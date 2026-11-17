import PrimeWindow

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section

/-- A fixed central dyadic interval, in numerical integers. -/
def band (N V : ℕ) := (Icc 0 N).filter fun u => 5*N ≤ 8*u ∧ 3*u ≤ 2*N ∧ V.Coprime u

def units (V : ℕ) := (range V).filter fun b => V.Coprime b

/-- For every fixed modulus V the central interval embeds in the disjoint
residue circles. The real interval occupies [5N/8,2N/3]. -/
theorem band_le_cells (K N V : ℕ) (vp : 0<V) (room : 64*V ≤ N) :
    let n:=N/V
    letI : NeZero n := ⟨(Nat.div_pos (by omega) vp).ne'⟩
    (∑ u∈band N V,classWeight K u) ≤
      ∑ b∈units V,∑ x:ZMod n,window K b V N x := by
  dsimp only
  classical
  let n:=N/V
  have hn : 0<n := Nat.div_pos (by omega) vp
  let _ : NeZero n := ⟨hn.ne'⟩
  let dest (u : ℕ) : ℕ × ZMod n := (u%V,((u/V:ℕ):ZMod n))
  let E := band N V
  let T := units V ×ˢ (univ : Finset (ZMod n))
  have data (u : ℕ) (hu : u∈E) : (dest u).2.val=u/V ∧ dest u∈T ∧
      window K (dest u).1 V N (dest u).2=classWeight K u := by
    obtain ⟨_,a,b,cp⟩ := mem_filter.mp hu
    have rem := Nat.mod_lt u vp
    have dec := Nat.mod_add_div u V
    have rd := Nat.mod_lt N vp
    have nd := Nat.mod_add_div N V
    have mid₁ : V*n ≤ V*(4*(u/V)) := by
      rw [show V*(4*(u/V))=4*(V*(u/V)) by ring]
      dsimp [n]
      omega
    have mid₂ : V*(4*(u/V)) < V*(3*n) := by
      rw [show V*(4*(u/V))=4*(V*(u/V)) by ring, show V*(3*n)=3*(V*n) by ring]
      dsimp [n]
      omega
    have lo := Nat.le_of_mul_le_mul_left mid₁ vp
    have hi := Nat.lt_of_mul_lt_mul_left mid₂
    have under : u/V<n := by omega
    have val : (dest u).2.val=u/V := ZMod.val_natCast_of_lt under
    have cop : V.Coprime (u%V) := by
      change V.gcd (u%V)=1
      rw [Nat.gcd_comm,←Nat.gcd_rec V u]
      exact cp
    have central : N/2 < u ∧ u ≤ N := by omega
    have v : u%V+V*(dest u).2.val=u := val ▸ dec
    refine ⟨val,mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr rem,cop⟩,mem_univ _⟩,?_⟩
    change (if N/2 < u%V+V*(dest u).2.val ∧ u%V+V*(dest u).2.val≤N ∧
        n≤4*(dest u).2.val ∧ 4*(dest u).2.val<3*n then classWeight K (u%V+V*(dest u).2.val) else 0)=_
    rw [v,val,ite_eq_left ⟨central.1,central.2,lo,hi⟩]
  have sub : E.image dest ⊆ T := by
    rintro _ hit
    obtain ⟨u,hu,rfl⟩:=mem_image.mp hit
    exact (data u hu).2.1
  have inj : Set.InjOn dest (↑E) := by
    intro u hu v hv eq
    have re : u%V=v%V := congrArg Prod.fst eq
    have va := congrArg (fun z : ℕ×ZMod n => z.2.val) eq
    rw [(data u hu).1,(data v hv).1] at va
    rw [←Nat.mod_add_div u V,←Nat.mod_add_div v V,re,va]
  calc
    _ = ∑ u∈E,window K (dest u).1 V N (dest u).2 := sum_congr rfl (fun u hu=>(data u hu).2.2.symm)
    _ = ∑ p∈E.image dest,window K p.1 V N p.2 := (sum_image (f:=fun p : ℕ×ZMod n => window K p.1 V N p.2) inj).symm
    _ ≤ ∑ p∈T,window K p.1 V N p.2 := sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by
      unfold window;split
      next => exact (class_weight_le _ _).1
      next => rfl)
    _ = _ := sum_product _ _ _

/-- φ(V)/V times the weight on one reduced residue class retains the original mean. -/
theorem exists_dense_class (K N V : ℕ) (vp : 0<V) (room : 64*V ≤ N)
    {η : ℝ} (ep : 0<η) (mass : η*N ≤ ∑ u∈band N V,classWeight K u) :
    let n:=N/V
    letI : NeZero n := ⟨(Nat.div_pos (by omega) vp).ne'⟩
    ∃ b∈units V, η*n ≤ ∑ x:ZMod n, ((V.totient:ℝ)/V)*window K b V N x := by
  dsimp only
  classical
  let n:=N/V
  have hn : 0<n := Nat.div_pos (by omega) vp
  let _ : NeZero n := ⟨hn.ne'⟩
  let L (b : ℕ) := ∑ x:ZMod n,window K b V N x
  have sumB := band_le_cells K N V vp room
  have Vn : (V:ℝ)*n ≤ N := by exact_mod_cast Nat.mul_div_le N V
  have ct : (units V).card=V.totient := (Nat.totient_eq_card_coprime V).symm
  have pos : 0 < V.totient := Nat.totient_pos.mpr vp
  have non : (units V).Nonempty := card_pos.mp (ct ▸ pos)
  by_contra! h
  have total := sum_lt_sum_of_nonempty non (fun b hb => h b hb)
  simp only [←mul_sum, sum_const, nsmul_eq_mul,ct] at total
  change (V.totient:ℝ)/V*(∑ b∈units V,L b) < _ at total
  have vr : (0:ℝ)<V := by exact_mod_cast vp
  have tr : (0:ℝ)<V.totient := by exact_mod_cast pos
  have small : ∑ b∈units V,L b < η*(V:ℝ)*n := by
    field_simp [vr.ne'] at total
    simpa [n,mul_comm (V:ℝ) η] using total
  have test : η*((V:ℝ)*n) ≤ η*N := mul_le_mul_of_nonneg_left Vn ep.le
  change (∑ u∈band N V,classWeight K u) ≤ ∑ b∈units V,L b at sumB
  have adjusted : η*(V:ℝ)*n ≤ η*N := by simpa only [mul_assoc] using test
  exact (not_lt_of_ge (mass.trans sumB)) (small.trans_le adjusted)

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.band_le_cells
#print axioms Sun28.PrimeTransfer.exists_dense_class
