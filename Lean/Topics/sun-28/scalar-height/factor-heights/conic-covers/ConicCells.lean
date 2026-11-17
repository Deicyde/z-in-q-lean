import ConicKernels

namespace Sun28.ConicCovers
open Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def row {R:Type*} [CommRing R] (s:Bool) (d a b:R) : Fin 4→R :=
  ![if s then 2*(b^2-a^2) else a^2-b^2,
    if s then 3*a^2+2398*b^2 else 343*a^2-439*b^2,
    (if s then 2 else 1)*d*(b+a)*(15*b-a),
    (if s then 14 else 5)*d*complementary s a b]

def integral (s:Bool) (d:ℕ) (a b:ℤ) := ∀i:Fin 4, ∃ y:ℤ, row s (d:ℤ) a b i=y^2

private def residues (s:Bool) (d p n:ℕ) [NeZero n] : Prop :=
  ∃ a b:ZMod n, (a.val%p≠0 ∨ b.val%p≠0) ∧ ∀i:Fin 4,row s (d:ZMod n) a b i∈squares n

private instance (s:Bool) (d p n:ℕ) [NeZero n] : Decidable (residues s d p n) := by
  unfold residues;infer_instance

private theorem passes {s:Bool} {d:ℕ} {a b:ℤ} (ab:a.natAbs.Coprime b.natAbs)
    (h:integral s d a b) {p n:ℕ} [NeZero n] (pp:p.Prime) (pn:p∣n) : residues s d p n := by
  refine ⟨a,b,?_,?_⟩
  · by_contra! z
    have cv (x:ℤ) (q:(x:ZMod n).val%p=0) : (p:ℤ)∣x := by
      have h':(p:ℤ)∣(n:ℤ):=by exact_mod_cast pn
      have ep:=ZMod.val_intCast (n:=n) x
      have ex:((x:ZMod n).val:ℤ) % (p:ℤ)=0 :=by exact_mod_cast q
      rw [ep,Int.emod_emod_of_dvd _ h'] at ex
      exact Int.dvd_of_emod_eq_zero ex
    exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr (cv a z.1))
      (by simpa using Int.natAbs_dvd_natAbs.mpr (cv b z.2))) ab
  · intro i
    obtain ⟨y,hy⟩:=h i
    apply Finset.mem_image.mpr
    refine ⟨(y:ZMod n),Finset.mem_univ _,?_⟩
    have E:=congrArg (Int.castRingHom (ZMod n)) hy
    cases s <;> fin_cases i <;> simpa [row,complementary,left] using E.symm

private theorem list9 (s:Bool) : ((210:ℕ).divisors.filter fun d=>residues s d 3 9)={2,5,14,35} := by
  cases s <;> decide

private theorem list16 : ({2,5,14,35}:Finset ℕ).filter (fun d=>residues true d 2 16)={2,14} := by decide
private theorem list32 : ({2,5,14,35}:Finset ℕ).filter (fun d=>residues false d 2 32)={5} := by decide

/-- The primitive mod-9 test and the mod-16 or mod-32 test leave three signed classes. -/
theorem surviving {s:Bool} {d:ℕ} {a b:ℤ} (ab:a.natAbs.Coprime b.natAbs)
    (dv:d∣210) (h:integral s d a b) :
    if s then d=2 ∨ d=14 else d=5 := by
  have v:=passes ab h (p:=3) (n:=9) (by decide) (by decide)
  have hit:d∈(210:ℕ).divisors.filter (fun k=>residues s k 3 9):=Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dv,by decide⟩,v⟩
  rw [list9] at hit
  cases s
  · have z:d∈({2,5,14,35}:Finset ℕ).filter (fun k=>residues false k 2 32):=Finset.mem_filter.mpr ⟨hit, passes ab h (p:=2) (n:=32) (by decide) (by decide)⟩
    rw [list32] at z;simpa using z
  · have z:d∈({2,5,14,35}:Finset ℕ).filter (fun k=>residues true k 2 16):=Finset.mem_filter.mpr ⟨hit, passes ab h (p:=2) (n:=16) (by decide) (by decide)⟩
    rw [list16] at z;simpa using z

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.surviving
