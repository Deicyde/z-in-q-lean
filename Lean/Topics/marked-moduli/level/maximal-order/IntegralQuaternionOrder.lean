import QuaternionOrder

/-! An integral membership test for the discriminant-six quaternion order. -/
namespace ZInQBlueprint.LevelThree
namespace IntegralOrder
noncomputable section

def embedHom : O →+* B where
  toFun := embed
  map_zero' := by ext <;> norm_num [embed]
  map_one' := by ext <;> norm_num [embed]
  map_mul' := embed_mul
  map_add' x y := by ext <;> simp [embed] <;> ring

def reducedNorm (q : B) : ℚ := (q * star q).re
def isInteger (t : ℚ) : Prop := ∃ n : ℤ, t = n

private def normForm {R : Type*} [CommRing R] (x y : R) := x^2 - x*y + y^2

/-- Local tests in the two residue fields give the four integer coordinates
in the basis 1, i, ω, iω. -/
private theorem coordinate_divisibility (a b c d n : ℤ)
    (h : 6*n = 2*normForm a c - normForm b d) :
    3 ∣ a+c ∧ 3 ∣ a-2*c ∧ 6 ∣ 2*b-d ∧ 6 ∣ 2*d-b := by
  have mod₂ : ∀ x y : ZMod 2, normForm x y = 0 → x = 0 ∧ y = 0 := by decide
  have mod₃ : ∀ w x y z : ZMod 3, 2*normForm w y - normForm x z = 0 →
      w+y=0 ∧ x+z=0 := by decide
  have e₂ := congrArg (fun t : ℤ => (t : ZMod 2)) h
  have e₃ := congrArg (fun t : ℤ => (t : ZMod 3)) h
  simp only [normForm,Int.cast_mul,Int.cast_add,Int.cast_sub,Int.cast_pow,Int.cast_ofNat] at e₂ e₃
  have hb₀ := mod₂ (b:ZMod 2) (d:ZMod 2) (by
    apply neg_eq_zero.mp
    simpa only [normForm, show (6:ZMod 2)=0 by decide, show (2:ZMod 2)=0 by decide,
      zero_mul,zero_sub] using e₂.symm)
  have h₃ := mod₃ (a:ZMod 3) (b:ZMod 3) (c:ZMod 3) (d:ZMod 3) (by
    simpa [normForm, show (6:ZMod 3)=0 by decide] using e₃.symm)
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hb₀.1
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).mp hb₀.2
  have hac := (ZMod.intCast_zmod_eq_zero_iff_dvd (a+c) 3).mp (by simpa using h₃.1)
  have hbd := (ZMod.intCast_zmod_eq_zero_iff_dvd (b+d) 3).mp (by simpa using h₃.2)
  omega

/-- A quaternion in the trace dual whose reduced norm is integral is in
the printed order. The four traces are paired with 1, i, ω, iω. -/
theorem mem_of_traces_norm (q : B)
    (h₀ : isInteger (trd q))
    (h₁ : isInteger (trd (q * embed (printed 0 1 0 0))))
    (h₂ : isInteger (trd (q * embed (printed 0 0 1 0))))
    (h₃ : isInteger (trd (q * embed (printed 0 0 0 1))))
    (hn : isInteger (reducedNorm q)) : ∃ x : O, embed x = q := by
  obtain ⟨a,ha⟩ := h₀
  obtain ⟨b,hb⟩ := h₁
  obtain ⟨c,hc⟩ := h₂
  obtain ⟨d,hd⟩ := h₃
  obtain ⟨n,hn'⟩ := hn
  rcases q with ⟨r,s,t,v⟩
  norm_num [trd,reducedNorm,embed_printed] at ha hb hc hd hn'
  have hid : (6:ℚ)*n = 2*normForm (a:ℚ) c - normForm (b:ℚ) d := by
    rw [←ha,←hb,←hc,←hd,←hn']
    unfold normForm
    ring
  have hi : 6*n = 2*normForm a c - normForm b d := by
    unfold normForm at hid ⊢
    exact_mod_cast hid
  obtain ⟨⟨i,hi⟩,⟨k,hk⟩,⟨j,hj⟩,⟨l,hl⟩⟩ := coordinate_divisibility a b c d n hi
  refine ⟨printed i j k l, ?_⟩
  rw [embed_printed]
  have ei : (a:ℚ)+c = 3*i := by exact_mod_cast hi
  have ej : 2*(b:ℚ)-d = 6*j := by exact_mod_cast hj
  have ek : (a:ℚ)-2*c = 3*k := by exact_mod_cast hk
  have el : 2*(d:ℚ)-b = 6*l := by exact_mod_cast hl
  ext <;> dsimp <;> linarith only [ha,hb,hc,hd,ei,ej,ek,el]

/-- Recover the *given* action as a ring isomorphism once the ambient
rational algebra and its integral reduced invariants have been identified. -/
def actionEquiv {E : Type*} [Ring E] (action : O →+* E) (realize : E →+* B)
    (faithful : Function.Injective realize) (compatible : ∀ x, realize (action x) = embed x)
    (trace : ∀ x, isInteger (trd (realize x)))
    (norm : ∀ x, isInteger (reducedNorm (realize x))) : O ≃+* E := by
  apply RingEquiv.ofBijective action
  constructor
  · intro x y h
    apply embed_injective
    simpa only [compatible] using congrArg realize h
  · intro y
    have pairing (x : O) : isInteger (trd (realize y * embed x)) := by
      simpa only [map_mul, compatible] using trace (y * action x)
    obtain ⟨x,h⟩ := mem_of_traces_norm (realize y) (trace y) (pairing _) (pairing _) (pairing _) (norm y)
    exact ⟨x,faithful ((compatible x).trans h)⟩

theorem actionEquiv_apply {E : Type*} [Ring E] (action : O →+* E) (realize : E →+* B)
    (faithful : Function.Injective realize) (compatible : ∀ x, realize (action x) = embed x)
    (trace : ∀ x, isInteger (trd (realize x))) (norm : ∀ x, isInteger (reducedNorm (realize x)))
    (x : O) : actionEquiv action realize faithful compatible trace norm x = action x := rfl

end
end IntegralOrder
end ZInQBlueprint.LevelThree
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.mem_of_traces_norm
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.actionEquiv
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.actionEquiv_apply
