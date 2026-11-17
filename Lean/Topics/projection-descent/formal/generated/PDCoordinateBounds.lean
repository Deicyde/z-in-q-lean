import PDSharedData
namespace ProjectionDescent.Shared
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
private abbrev goodAt (i : Nat) := live15 i=true → 1≤code i ∧ code i≤226 ∧ back (code i)=i
private theorem segment0 : ∀ j : Fin 8, goodAt (j.val+0) := by unfold goodAt; decide
private theorem segment8 : ∀ j : Fin 8, goodAt (j.val+8) := by unfold goodAt; decide
private theorem segment16 : ∀ j : Fin 8, goodAt (j.val+16) := by unfold goodAt; decide
private theorem segment24 : ∀ j : Fin 8, goodAt (j.val+24) := by unfold goodAt; decide
private theorem segment32 : ∀ j : Fin 8, goodAt (j.val+32) := by unfold goodAt; decide
private theorem segment40 : ∀ j : Fin 8, goodAt (j.val+40) := by unfold goodAt; decide
private theorem segment48 : ∀ j : Fin 8, goodAt (j.val+48) := by unfold goodAt; decide
private theorem segment56 : ∀ j : Fin 8, goodAt (j.val+56) := by unfold goodAt; decide
private theorem segment64 : ∀ j : Fin 8, goodAt (j.val+64) := by unfold goodAt; decide
private theorem segment72 : ∀ j : Fin 8, goodAt (j.val+72) := by unfold goodAt; decide
private theorem segment80 : ∀ j : Fin 8, goodAt (j.val+80) := by unfold goodAt; decide
private theorem segment88 : ∀ j : Fin 8, goodAt (j.val+88) := by unfold goodAt; decide
private theorem segment96 : ∀ j : Fin 8, goodAt (j.val+96) := by unfold goodAt; decide
private theorem segment104 : ∀ j : Fin 8, goodAt (j.val+104) := by unfold goodAt; decide
private theorem segment112 : ∀ j : Fin 8, goodAt (j.val+112) := by unfold goodAt; decide
private theorem segment120 : ∀ j : Fin 8, goodAt (j.val+120) := by unfold goodAt; decide
private theorem segment128 : ∀ j : Fin 8, goodAt (j.val+128) := by unfold goodAt; decide
private theorem segment136 : ∀ j : Fin 8, goodAt (j.val+136) := by unfold goodAt; decide
private theorem segment144 : ∀ j : Fin 8, goodAt (j.val+144) := by unfold goodAt; decide
private theorem segment152 : ∀ j : Fin 8, goodAt (j.val+152) := by unfold goodAt; decide
private theorem segment160 : ∀ j : Fin 8, goodAt (j.val+160) := by unfold goodAt; decide
private theorem segment168 : ∀ j : Fin 8, goodAt (j.val+168) := by unfold goodAt; decide
private theorem segment176 : ∀ j : Fin 8, goodAt (j.val+176) := by unfold goodAt; decide
private theorem segment184 : ∀ j : Fin 8, goodAt (j.val+184) := by unfold goodAt; decide
private theorem segment192 : ∀ j : Fin 8, goodAt (j.val+192) := by unfold goodAt; decide
private theorem segment200 : ∀ j : Fin 8, goodAt (j.val+200) := by unfold goodAt; decide
private theorem segment208 : ∀ j : Fin 8, goodAt (j.val+208) := by unfold goodAt; decide
private theorem segment216 : ∀ j : Fin 8, goodAt (j.val+216) := by unfold goodAt; decide
private theorem segment224 : ∀ j : Fin 8, goodAt (j.val+224) := by unfold goodAt; decide
private theorem segment232 : ∀ j : Fin 8, goodAt (j.val+232) := by unfold goodAt; decide
private theorem segment240 : ∀ j : Fin 8, goodAt (j.val+240) := by unfold goodAt; decide
private theorem segment248 : ∀ j : Fin 8, goodAt (j.val+248) := by unfold goodAt; decide
theorem coordinate_bounds (i : Nat) (hi : live15 i=true) : 1≤code i ∧ code i≤226 ∧ back (code i)=i := by
  have lim : i≤249 := by
    simp only [live15,live14,live13,live12,live11,live10,live9,live8,live7,live6,live5,live4,live3,live2,live1,dropSlot,poleLive,live0,Bool.and_eq_true,decide_eq_true_eq] at hi; omega
  by_cases h0 : i<8
  · have row := segment0 ⟨i-0,by omega⟩; change goodAt ((i-0)+0) at row; rw [show i-0+0=i by omega] at row; exact row hi
  by_cases h8 : i<16
  · have row := segment8 ⟨i-8,by omega⟩; change goodAt ((i-8)+8) at row; rw [show i-8+8=i by omega] at row; exact row hi
  by_cases h16 : i<24
  · have row := segment16 ⟨i-16,by omega⟩; change goodAt ((i-16)+16) at row; rw [show i-16+16=i by omega] at row; exact row hi
  by_cases h24 : i<32
  · have row := segment24 ⟨i-24,by omega⟩; change goodAt ((i-24)+24) at row; rw [show i-24+24=i by omega] at row; exact row hi
  by_cases h32 : i<40
  · have row := segment32 ⟨i-32,by omega⟩; change goodAt ((i-32)+32) at row; rw [show i-32+32=i by omega] at row; exact row hi
  by_cases h40 : i<48
  · have row := segment40 ⟨i-40,by omega⟩; change goodAt ((i-40)+40) at row; rw [show i-40+40=i by omega] at row; exact row hi
  by_cases h48 : i<56
  · have row := segment48 ⟨i-48,by omega⟩; change goodAt ((i-48)+48) at row; rw [show i-48+48=i by omega] at row; exact row hi
  by_cases h56 : i<64
  · have row := segment56 ⟨i-56,by omega⟩; change goodAt ((i-56)+56) at row; rw [show i-56+56=i by omega] at row; exact row hi
  by_cases h64 : i<72
  · have row := segment64 ⟨i-64,by omega⟩; change goodAt ((i-64)+64) at row; rw [show i-64+64=i by omega] at row; exact row hi
  by_cases h72 : i<80
  · have row := segment72 ⟨i-72,by omega⟩; change goodAt ((i-72)+72) at row; rw [show i-72+72=i by omega] at row; exact row hi
  by_cases h80 : i<88
  · have row := segment80 ⟨i-80,by omega⟩; change goodAt ((i-80)+80) at row; rw [show i-80+80=i by omega] at row; exact row hi
  by_cases h88 : i<96
  · have row := segment88 ⟨i-88,by omega⟩; change goodAt ((i-88)+88) at row; rw [show i-88+88=i by omega] at row; exact row hi
  by_cases h96 : i<104
  · have row := segment96 ⟨i-96,by omega⟩; change goodAt ((i-96)+96) at row; rw [show i-96+96=i by omega] at row; exact row hi
  by_cases h104 : i<112
  · have row := segment104 ⟨i-104,by omega⟩; change goodAt ((i-104)+104) at row; rw [show i-104+104=i by omega] at row; exact row hi
  by_cases h112 : i<120
  · have row := segment112 ⟨i-112,by omega⟩; change goodAt ((i-112)+112) at row; rw [show i-112+112=i by omega] at row; exact row hi
  by_cases h120 : i<128
  · have row := segment120 ⟨i-120,by omega⟩; change goodAt ((i-120)+120) at row; rw [show i-120+120=i by omega] at row; exact row hi
  by_cases h128 : i<136
  · have row := segment128 ⟨i-128,by omega⟩; change goodAt ((i-128)+128) at row; rw [show i-128+128=i by omega] at row; exact row hi
  by_cases h136 : i<144
  · have row := segment136 ⟨i-136,by omega⟩; change goodAt ((i-136)+136) at row; rw [show i-136+136=i by omega] at row; exact row hi
  by_cases h144 : i<152
  · have row := segment144 ⟨i-144,by omega⟩; change goodAt ((i-144)+144) at row; rw [show i-144+144=i by omega] at row; exact row hi
  by_cases h152 : i<160
  · have row := segment152 ⟨i-152,by omega⟩; change goodAt ((i-152)+152) at row; rw [show i-152+152=i by omega] at row; exact row hi
  by_cases h160 : i<168
  · have row := segment160 ⟨i-160,by omega⟩; change goodAt ((i-160)+160) at row; rw [show i-160+160=i by omega] at row; exact row hi
  by_cases h168 : i<176
  · have row := segment168 ⟨i-168,by omega⟩; change goodAt ((i-168)+168) at row; rw [show i-168+168=i by omega] at row; exact row hi
  by_cases h176 : i<184
  · have row := segment176 ⟨i-176,by omega⟩; change goodAt ((i-176)+176) at row; rw [show i-176+176=i by omega] at row; exact row hi
  by_cases h184 : i<192
  · have row := segment184 ⟨i-184,by omega⟩; change goodAt ((i-184)+184) at row; rw [show i-184+184=i by omega] at row; exact row hi
  by_cases h192 : i<200
  · have row := segment192 ⟨i-192,by omega⟩; change goodAt ((i-192)+192) at row; rw [show i-192+192=i by omega] at row; exact row hi
  by_cases h200 : i<208
  · have row := segment200 ⟨i-200,by omega⟩; change goodAt ((i-200)+200) at row; rw [show i-200+200=i by omega] at row; exact row hi
  by_cases h208 : i<216
  · have row := segment208 ⟨i-208,by omega⟩; change goodAt ((i-208)+208) at row; rw [show i-208+208=i by omega] at row; exact row hi
  by_cases h216 : i<224
  · have row := segment216 ⟨i-216,by omega⟩; change goodAt ((i-216)+216) at row; rw [show i-216+216=i by omega] at row; exact row hi
  by_cases h224 : i<232
  · have row := segment224 ⟨i-224,by omega⟩; change goodAt ((i-224)+224) at row; rw [show i-224+224=i by omega] at row; exact row hi
  by_cases h232 : i<240
  · have row := segment232 ⟨i-232,by omega⟩; change goodAt ((i-232)+232) at row; rw [show i-232+232=i by omega] at row; exact row hi
  by_cases h240 : i<248
  · have row := segment240 ⟨i-240,by omega⟩; change goodAt ((i-240)+240) at row; rw [show i-240+240=i by omega] at row; exact row hi
  have row := segment248 ⟨i-248,by omega⟩; change goodAt ((i-248)+248) at row; rw [show i-248+248=i by omega] at row; exact row hi
end ProjectionDescent.Shared
