import TriRanks1
open ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1300000
theorem range160 : ∀ j : Fin 8, boundAt (j.val+160) := by unfold boundAt; decide
theorem range168 : ∀ j : Fin 8, boundAt (j.val+168) := by unfold boundAt; decide
theorem range176 : ∀ j : Fin 8, boundAt (j.val+176) := by unfold boundAt; decide
theorem range184 : ∀ j : Fin 8, boundAt (j.val+184) := by unfold boundAt; decide
theorem range192 : ∀ j : Fin 8, boundAt (j.val+192) := by unfold boundAt; decide
theorem range200 : ∀ j : Fin 8, boundAt (j.val+200) := by unfold boundAt; decide
theorem range208 : ∀ j : Fin 8, boundAt (j.val+208) := by unfold boundAt; decide
theorem range216 : ∀ j : Fin 8, boundAt (j.val+216) := by unfold boundAt; decide
theorem range224 : ∀ j : Fin 8, boundAt (j.val+224) := by unfold boundAt; decide
theorem rangeTable (g : Bool) (i : Nat) (hi : inside i=true) (hn : i∉slots (ps g)) : 1≤code i ∧ code i≤153 ∧ back (code i)=i := by
  unfold ps at hn; rw [slots0] at hn
  have lim : 1≤i ∧ i≤226 := of_decide_eq_true hi
  by_cases h0 : i<8
  · have h := range0 ⟨i-0,by omega⟩; change boundAt ((i-0)+0) at h; rw [show i-0+0=i by omega] at h; exact h hi hn
  by_cases h8 : i<16
  · have h := range8 ⟨i-8,by omega⟩; change boundAt ((i-8)+8) at h; rw [show i-8+8=i by omega] at h; exact h hi hn
  by_cases h16 : i<24
  · have h := range16 ⟨i-16,by omega⟩; change boundAt ((i-16)+16) at h; rw [show i-16+16=i by omega] at h; exact h hi hn
  by_cases h24 : i<32
  · have h := range24 ⟨i-24,by omega⟩; change boundAt ((i-24)+24) at h; rw [show i-24+24=i by omega] at h; exact h hi hn
  by_cases h32 : i<40
  · have h := range32 ⟨i-32,by omega⟩; change boundAt ((i-32)+32) at h; rw [show i-32+32=i by omega] at h; exact h hi hn
  by_cases h40 : i<48
  · have h := range40 ⟨i-40,by omega⟩; change boundAt ((i-40)+40) at h; rw [show i-40+40=i by omega] at h; exact h hi hn
  by_cases h48 : i<56
  · have h := range48 ⟨i-48,by omega⟩; change boundAt ((i-48)+48) at h; rw [show i-48+48=i by omega] at h; exact h hi hn
  by_cases h56 : i<64
  · have h := range56 ⟨i-56,by omega⟩; change boundAt ((i-56)+56) at h; rw [show i-56+56=i by omega] at h; exact h hi hn
  by_cases h64 : i<72
  · have h := range64 ⟨i-64,by omega⟩; change boundAt ((i-64)+64) at h; rw [show i-64+64=i by omega] at h; exact h hi hn
  by_cases h72 : i<80
  · have h := range72 ⟨i-72,by omega⟩; change boundAt ((i-72)+72) at h; rw [show i-72+72=i by omega] at h; exact h hi hn
  by_cases h80 : i<88
  · have h := range80 ⟨i-80,by omega⟩; change boundAt ((i-80)+80) at h; rw [show i-80+80=i by omega] at h; exact h hi hn
  by_cases h88 : i<96
  · have h := range88 ⟨i-88,by omega⟩; change boundAt ((i-88)+88) at h; rw [show i-88+88=i by omega] at h; exact h hi hn
  by_cases h96 : i<104
  · have h := range96 ⟨i-96,by omega⟩; change boundAt ((i-96)+96) at h; rw [show i-96+96=i by omega] at h; exact h hi hn
  by_cases h104 : i<112
  · have h := range104 ⟨i-104,by omega⟩; change boundAt ((i-104)+104) at h; rw [show i-104+104=i by omega] at h; exact h hi hn
  by_cases h112 : i<120
  · have h := range112 ⟨i-112,by omega⟩; change boundAt ((i-112)+112) at h; rw [show i-112+112=i by omega] at h; exact h hi hn
  by_cases h120 : i<128
  · have h := range120 ⟨i-120,by omega⟩; change boundAt ((i-120)+120) at h; rw [show i-120+120=i by omega] at h; exact h hi hn
  by_cases h128 : i<136
  · have h := range128 ⟨i-128,by omega⟩; change boundAt ((i-128)+128) at h; rw [show i-128+128=i by omega] at h; exact h hi hn
  by_cases h136 : i<144
  · have h := range136 ⟨i-136,by omega⟩; change boundAt ((i-136)+136) at h; rw [show i-136+136=i by omega] at h; exact h hi hn
  by_cases h144 : i<152
  · have h := range144 ⟨i-144,by omega⟩; change boundAt ((i-144)+144) at h; rw [show i-144+144=i by omega] at h; exact h hi hn
  by_cases h152 : i<160
  · have h := range152 ⟨i-152,by omega⟩; change boundAt ((i-152)+152) at h; rw [show i-152+152=i by omega] at h; exact h hi hn
  by_cases h160 : i<168
  · have h := range160 ⟨i-160,by omega⟩; change boundAt ((i-160)+160) at h; rw [show i-160+160=i by omega] at h; exact h hi hn
  by_cases h168 : i<176
  · have h := range168 ⟨i-168,by omega⟩; change boundAt ((i-168)+168) at h; rw [show i-168+168=i by omega] at h; exact h hi hn
  by_cases h176 : i<184
  · have h := range176 ⟨i-176,by omega⟩; change boundAt ((i-176)+176) at h; rw [show i-176+176=i by omega] at h; exact h hi hn
  by_cases h184 : i<192
  · have h := range184 ⟨i-184,by omega⟩; change boundAt ((i-184)+184) at h; rw [show i-184+184=i by omega] at h; exact h hi hn
  by_cases h192 : i<200
  · have h := range192 ⟨i-192,by omega⟩; change boundAt ((i-192)+192) at h; rw [show i-192+192=i by omega] at h; exact h hi hn
  by_cases h200 : i<208
  · have h := range200 ⟨i-200,by omega⟩; change boundAt ((i-200)+200) at h; rw [show i-200+200=i by omega] at h; exact h hi hn
  by_cases h208 : i<216
  · have h := range208 ⟨i-208,by omega⟩; change boundAt ((i-208)+208) at h; rw [show i-208+208=i by omega] at h; exact h hi hn
  by_cases h216 : i<224
  · have h := range216 ⟨i-216,by omega⟩; change boundAt ((i-216)+216) at h; rw [show i-216+216=i by omega] at h; exact h hi hn
  have h := range224 ⟨i-224,by omega⟩; change boundAt ((i-224)+224) at h; rw [show i-224+224=i by omega] at h; exact h hi hn
end Triangular.Data
