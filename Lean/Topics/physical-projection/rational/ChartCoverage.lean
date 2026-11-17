import ChartSupport
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 7000
set_option maxHeartbeats 1000000

def pivotSlots : List Nat := [120, 121, 189, 175, 188, 190, 197, 198, 186, 187, 199, 142, 191, 180, 181, 192, 78, 79, 193, 182, 183, 194, 88, 89, 195, 196, 184, 185, 201, 200, 202, 130, 131, 132, 145, 146, 209, 210, 211, 154, 203, 204, 205, 206, 207, 208, 213, 212, 214, 133, 134, 157, 158, 221, 222, 223, 166, 215, 216, 217, 218, 219, 220, 225, 224, 226, 169, 178, 179, 94, 95, 100, 101]
theorem slot_numbers (g : Bool) : slots (ps g)=pivotSlots := by unfold ps;rw [slots0];rfl
def isCovered (i : Nat) : Bool := pivotSlots.contains i || !(inside i) || !(visible i) || changed.contains i || parentSlots.contains i
theorem checking0 : ∀ j : Fin 12, isCovered (j.val+0)=true := by decide
theorem checking12 : ∀ j : Fin 12, isCovered (j.val+12)=true := by decide
theorem checking24 : ∀ j : Fin 12, isCovered (j.val+24)=true := by decide
theorem checking36 : ∀ j : Fin 12, isCovered (j.val+36)=true := by decide
theorem checking48 : ∀ j : Fin 12, isCovered (j.val+48)=true := by decide
theorem checking60 : ∀ j : Fin 12, isCovered (j.val+60)=true := by decide
theorem checking72 : ∀ j : Fin 12, isCovered (j.val+72)=true := by decide
theorem checking84 : ∀ j : Fin 12, isCovered (j.val+84)=true := by decide
theorem checking96 : ∀ j : Fin 12, isCovered (j.val+96)=true := by decide
theorem checking108 : ∀ j : Fin 12, isCovered (j.val+108)=true := by decide
theorem checking120 : ∀ j : Fin 12, isCovered (j.val+120)=true := by decide
theorem checking132 : ∀ j : Fin 12, isCovered (j.val+132)=true := by decide
theorem checking144 : ∀ j : Fin 12, isCovered (j.val+144)=true := by decide
theorem checking156 : ∀ j : Fin 12, isCovered (j.val+156)=true := by decide
theorem checking168 : ∀ j : Fin 12, isCovered (j.val+168)=true := by decide
theorem checking180 : ∀ j : Fin 12, isCovered (j.val+180)=true := by decide
theorem checking192 : ∀ j : Fin 12, isCovered (j.val+192)=true := by decide
theorem checking204 : ∀ j : Fin 12, isCovered (j.val+204)=true := by decide
theorem checking216 : ∀ j : Fin 12, isCovered (j.val+216)=true := by decide

theorem covered (g : Bool) {i : Nat} (ok : inside i=true) (v : visible i=true) (hf : i∉slots (ps g)) (hc : i∉changed) : i∈parentSlots := by
  have bound : i<227 := by have := of_decide_eq_true ok; omega
  have table : isCovered i=true := by
    by_cases t0 : i<12
    · have q:=checking0 ⟨i-0,by omega⟩; change isCovered (i-0+0)=true at q; rwa [show i-0+0=i by omega] at q
    by_cases t12 : i<24
    · have q:=checking12 ⟨i-12,by omega⟩; change isCovered (i-12+12)=true at q; rwa [show i-12+12=i by omega] at q
    by_cases t24 : i<36
    · have q:=checking24 ⟨i-24,by omega⟩; change isCovered (i-24+24)=true at q; rwa [show i-24+24=i by omega] at q
    by_cases t36 : i<48
    · have q:=checking36 ⟨i-36,by omega⟩; change isCovered (i-36+36)=true at q; rwa [show i-36+36=i by omega] at q
    by_cases t48 : i<60
    · have q:=checking48 ⟨i-48,by omega⟩; change isCovered (i-48+48)=true at q; rwa [show i-48+48=i by omega] at q
    by_cases t60 : i<72
    · have q:=checking60 ⟨i-60,by omega⟩; change isCovered (i-60+60)=true at q; rwa [show i-60+60=i by omega] at q
    by_cases t72 : i<84
    · have q:=checking72 ⟨i-72,by omega⟩; change isCovered (i-72+72)=true at q; rwa [show i-72+72=i by omega] at q
    by_cases t84 : i<96
    · have q:=checking84 ⟨i-84,by omega⟩; change isCovered (i-84+84)=true at q; rwa [show i-84+84=i by omega] at q
    by_cases t96 : i<108
    · have q:=checking96 ⟨i-96,by omega⟩; change isCovered (i-96+96)=true at q; rwa [show i-96+96=i by omega] at q
    by_cases t108 : i<120
    · have q:=checking108 ⟨i-108,by omega⟩; change isCovered (i-108+108)=true at q; rwa [show i-108+108=i by omega] at q
    by_cases t120 : i<132
    · have q:=checking120 ⟨i-120,by omega⟩; change isCovered (i-120+120)=true at q; rwa [show i-120+120=i by omega] at q
    by_cases t132 : i<144
    · have q:=checking132 ⟨i-132,by omega⟩; change isCovered (i-132+132)=true at q; rwa [show i-132+132=i by omega] at q
    by_cases t144 : i<156
    · have q:=checking144 ⟨i-144,by omega⟩; change isCovered (i-144+144)=true at q; rwa [show i-144+144=i by omega] at q
    by_cases t156 : i<168
    · have q:=checking156 ⟨i-156,by omega⟩; change isCovered (i-156+156)=true at q; rwa [show i-156+156=i by omega] at q
    by_cases t168 : i<180
    · have q:=checking168 ⟨i-168,by omega⟩; change isCovered (i-168+168)=true at q; rwa [show i-168+168=i by omega] at q
    by_cases t180 : i<192
    · have q:=checking180 ⟨i-180,by omega⟩; change isCovered (i-180+180)=true at q; rwa [show i-180+180=i by omega] at q
    by_cases t192 : i<204
    · have q:=checking192 ⟨i-192,by omega⟩; change isCovered (i-192+192)=true at q; rwa [show i-192+192=i by omega] at q
    by_cases t204 : i<216
    · have q:=checking204 ⟨i-204,by omega⟩; change isCovered (i-204+204)=true at q; rwa [show i-204+204=i by omega] at q
    have q:=checking216 ⟨i-216,by omega⟩; change isCovered (i-216+216)=true at q; rwa [show i-216+216=i by omega] at q
  rw [slot_numbers] at hf; simpa [isCovered,ok,v,hf,hc] using table
end PhysicalProjection
