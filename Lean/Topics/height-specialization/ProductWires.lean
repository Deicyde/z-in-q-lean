import PhysicalSlope
namespace HeightSpecialization
open CircuitTransport StructuralReduction StructuralReduction.Transfer84
open PhysicalProjection.Comparison ProjectionFibres.Comparison ProjectionFibres.HeightSupport
set_option linter.unusedSimpArgs false
private theorem e1 (x : Fin 84→Rat) : (atWire x 1)=cell x 2 :=
  wireStep x (by decide) (show patch archiveAt 1=.var 2 from rfl) trivial
private theorem e2 (x : Fin 84→Rat) : (atWire x 2)=cell x 3 :=
  wireStep x (by decide) (show patch archiveAt 2=.var 3 from rfl) trivial
private theorem e4 (x : Fin 84→Rat) : (atWire x 4)=cell x 5 :=
  wireStep x (by decide) (show patch archiveAt 4=.var 5 from rfl) trivial
private theorem e5 (x : Fin 84→Rat) : (atWire x 5)=cell x 6 :=
  wireStep x (by decide) (show patch archiveAt 5=.var 6 from rfl) trivial
private theorem e6 (x : Fin 84→Rat) : (atWire x 6)=cell x 7 :=
  wireStep x (by decide) (show patch archiveAt 6=.var 7 from rfl) trivial
private theorem e7 (x : Fin 84→Rat) : (atWire x 7)=cell x 8 :=
  wireStep x (by decide) (show patch archiveAt 7=.var 8 from rfl) trivial
private theorem e9 (x : Fin 84→Rat) : (atWire x 9)=cell x 10 :=
  wireStep x (by decide) (show patch archiveAt 9=.var 10 from rfl) trivial
private theorem e10 (x : Fin 84→Rat) : (atWire x 10)=cell x 11 :=
  wireStep x (by decide) (show patch archiveAt 10=.var 11 from rfl) trivial
private theorem e85 (x : Fin 84→Rat) : (atWire x 85)=(2:Rat) :=
  wireStep x (by decide) (show patch archiveAt 85=.int 2 from rfl) trivial
private theorem e114 (x : Fin 84→Rat) : (atWire x 114)=(atWire x 1)*(atWire x 1) :=
  wireStep x (by decide) (show patch archiveAt 114=.mul 1 1 from rfl) ⟨by decide,by decide⟩
private theorem e120 (x : Fin 84→Rat) : (atWire x 120)=(atWire x 1)*(atWire x 2) :=
  wireStep x (by decide) (show patch archiveAt 120=.mul 1 2 from rfl) ⟨by decide,by decide⟩
private theorem e121 (x : Fin 84→Rat) : (atWire x 121)=(atWire x 120)+(atWire x 120) :=
  wireStep x (by decide) (show patch archiveAt 121=.add 120 120 from rfl) ⟨by decide,by decide⟩
private theorem e150 (x : Fin 84→Rat) : (atWire x 150)=(atWire x 9)*(atWire x 9) :=
  wireStep x (by decide) (show patch archiveAt 150=.mul 9 9 from rfl) ⟨by decide,by decide⟩
private theorem e154 (x : Fin 84→Rat) : (atWire x 154)=(atWire x 9)*(atWire x 10) :=
  wireStep x (by decide) (show patch archiveAt 154=.mul 9 10 from rfl) ⟨by decide,by decide⟩
private theorem e155 (x : Fin 84→Rat) : (atWire x 155)=(atWire x 154)+(atWire x 154) :=
  wireStep x (by decide) (show patch archiveAt 155=.add 154 154 from rfl) ⟨by decide,by decide⟩
private theorem e156 (x : Fin 84→Rat) : (atWire x 156)=(atWire x 6)*(atWire x 6) :=
  wireStep x (by decide) (show patch archiveAt 156=.mul 6 6 from rfl) ⟨by decide,by decide⟩
private theorem e160 (x : Fin 84→Rat) : (atWire x 160)=(atWire x 6)*(atWire x 7) :=
  wireStep x (by decide) (show patch archiveAt 160=.mul 6 7 from rfl) ⟨by decide,by decide⟩
private theorem e161 (x : Fin 84→Rat) : (atWire x 161)=(atWire x 160)+(atWire x 160) :=
  wireStep x (by decide) (show patch archiveAt 161=.add 160 160 from rfl) ⟨by decide,by decide⟩
private theorem e182 (x : Fin 84→Rat) : (atWire x 182)=(5070054779947717629308371384521789480239396134271756906351118151050703599166632466437044672432923755120388312614740520104204175287618362020963:Rat) :=
  wireStep x (by decide) (show patch archiveAt 182=.int 5070054779947717629308371384521789480239396134271756906351118151050703599166632466437044672432923755120388312614740520104204175287618362020963 from rfl) trivial
private theorem e183 (x : Fin 84→Rat) : (atWire x 183)=(atWire x 4)*(atWire x 182) :=
  wireStep x (by decide) (show patch archiveAt 183=.mul 4 182 from rfl) ⟨by decide,by decide⟩
private theorem e184 (x : Fin 84→Rat) : (atWire x 184)=(atWire x 183)*(atWire x 183) :=
  wireStep x (by decide) (show patch archiveAt 184=.mul 183 183 from rfl) ⟨by decide,by decide⟩
private theorem e185 (x : Fin 84→Rat) : (atWire x 185)=(atWire x 5)*(atWire x 182) :=
  wireStep x (by decide) (show patch archiveAt 185=.mul 5 182 from rfl) ⟨by decide,by decide⟩
private theorem e189 (x : Fin 84→Rat) : (atWire x 189)=(atWire x 183)*(atWire x 185) :=
  wireStep x (by decide) (show patch archiveAt 189=.mul 183 185 from rfl) ⟨by decide,by decide⟩
private theorem e190 (x : Fin 84→Rat) : (atWire x 190)=(atWire x 189)+(atWire x 189) :=
  wireStep x (by decide) (show patch archiveAt 190=.add 189 189 from rfl) ⟨by decide,by decide⟩
private theorem e1073 (x : Fin 84→Rat) : (atWire x 1073)=(atWire x 2)*(atWire x 85) :=
  wireStep x (by decide) (show patch archiveAt 1073=.mul 2 85 from rfl) ⟨by decide,by decide⟩
private theorem e1074 (x : Fin 84→Rat) : (atWire x 1074)=(atWire x 2)*(atWire x 1073) :=
  wireStep x (by decide) (show patch archiveAt 1074=.mul 2 1073 from rfl) ⟨by decide,by decide⟩
private theorem e1075 (x : Fin 84→Rat) : (atWire x 1075)=(atWire x 114)+(atWire x 1074) :=
  wireStep x (by decide) (show patch archiveAt 1075=.add 114 1074 from rfl) ⟨by decide,by decide⟩
private theorem e1077 (x : Fin 84→Rat) : (atWire x 1077)=(atWire x 85)*(atWire x 121) :=
  wireStep x (by decide) (show patch archiveAt 1077=.mul 85 121 from rfl) ⟨by decide,by decide⟩
private theorem e1116 (x : Fin 84→Rat) : (atWire x 1116)=(atWire x 85)*(atWire x 185) :=
  wireStep x (by decide) (show patch archiveAt 1116=.mul 85 185 from rfl) ⟨by decide,by decide⟩
private theorem e1117 (x : Fin 84→Rat) : (atWire x 1117)=(atWire x 185)*(atWire x 1116) :=
  wireStep x (by decide) (show patch archiveAt 1117=.mul 185 1116 from rfl) ⟨by decide,by decide⟩
private theorem e1118 (x : Fin 84→Rat) : (atWire x 1118)=(atWire x 184)+(atWire x 1117) :=
  wireStep x (by decide) (show patch archiveAt 1118=.add 184 1117 from rfl) ⟨by decide,by decide⟩
private theorem e1155 (x : Fin 84→Rat) : (atWire x 1155)=(atWire x 1075)*(atWire x 1118) :=
  wireStep x (by decide) (show patch archiveAt 1155=.mul 1075 1118 from rfl) ⟨by decide,by decide⟩
private theorem e1156 (x : Fin 84→Rat) : (atWire x 1156)=(atWire x 190)*(atWire x 1077) :=
  wireStep x (by decide) (show patch archiveAt 1156=.mul 190 1077 from rfl) ⟨by decide,by decide⟩
private theorem e1157 (x : Fin 84→Rat) : (atWire x 1157)=(atWire x 1155)+(atWire x 1156) :=
  wireStep x (by decide) (show patch archiveAt 1157=.add 1155 1156 from rfl) ⟨by decide,by decide⟩
private theorem e1158 (x : Fin 84→Rat) : (atWire x 1158)=(atWire x 190)*(atWire x 1075) :=
  wireStep x (by decide) (show patch archiveAt 1158=.mul 190 1075 from rfl) ⟨by decide,by decide⟩
private theorem e1159 (x : Fin 84→Rat) : (atWire x 1159)=(atWire x 121)*(atWire x 1118) :=
  wireStep x (by decide) (show patch archiveAt 1159=.mul 121 1118 from rfl) ⟨by decide,by decide⟩
private theorem e1160 (x : Fin 84→Rat) : (atWire x 1160)=(atWire x 1158)+(atWire x 1159) :=
  wireStep x (by decide) (show patch archiveAt 1160=.add 1158 1159 from rfl) ⟨by decide,by decide⟩
private theorem e1161 (x : Fin 84→Rat) : (atWire x 1161)=(atWire x 7)*(atWire x 85) :=
  wireStep x (by decide) (show patch archiveAt 1161=.mul 7 85 from rfl) ⟨by decide,by decide⟩
private theorem e1162 (x : Fin 84→Rat) : (atWire x 1162)=(atWire x 7)*(atWire x 1161) :=
  wireStep x (by decide) (show patch archiveAt 1162=.mul 7 1161 from rfl) ⟨by decide,by decide⟩
private theorem e1163 (x : Fin 84→Rat) : (atWire x 1163)=(atWire x 156)+(atWire x 1162) :=
  wireStep x (by decide) (show patch archiveAt 1163=.add 156 1162 from rfl) ⟨by decide,by decide⟩
private theorem e1200 (x : Fin 84→Rat) : (atWire x 1200)=(atWire x 1157)*(atWire x 1163) :=
  wireStep x (by decide) (show patch archiveAt 1200=.mul 1157 1163 from rfl) ⟨by decide,by decide⟩
private theorem e1201 (x : Fin 84→Rat) : (atWire x 1201)=(atWire x 85)*(atWire x 1160) :=
  wireStep x (by decide) (show patch archiveAt 1201=.mul 85 1160 from rfl) ⟨by decide,by decide⟩
private theorem e1202 (x : Fin 84→Rat) : (atWire x 1202)=(atWire x 161)*(atWire x 1201) :=
  wireStep x (by decide) (show patch archiveAt 1202=.mul 161 1201 from rfl) ⟨by decide,by decide⟩
private theorem e1203 (x : Fin 84→Rat) : (atWire x 1203)=(atWire x 1200)+(atWire x 1202) :=
  wireStep x (by decide) (show patch archiveAt 1203=.add 1200 1202 from rfl) ⟨by decide,by decide⟩
private theorem e1204 (x : Fin 84→Rat) : (atWire x 1204)=(atWire x 161)*(atWire x 1157) :=
  wireStep x (by decide) (show patch archiveAt 1204=.mul 161 1157 from rfl) ⟨by decide,by decide⟩
private theorem e1205 (x : Fin 84→Rat) : (atWire x 1205)=(atWire x 1160)*(atWire x 1163) :=
  wireStep x (by decide) (show patch archiveAt 1205=.mul 1160 1163 from rfl) ⟨by decide,by decide⟩
private theorem e1206 (x : Fin 84→Rat) : (atWire x 1206)=(atWire x 1204)+(atWire x 1205) :=
  wireStep x (by decide) (show patch archiveAt 1206=.add 1204 1205 from rfl) ⟨by decide,by decide⟩
private theorem e1207 (x : Fin 84→Rat) : (atWire x 1207)=(atWire x 10)*(atWire x 85) :=
  wireStep x (by decide) (show patch archiveAt 1207=.mul 10 85 from rfl) ⟨by decide,by decide⟩
private theorem e1208 (x : Fin 84→Rat) : (atWire x 1208)=(atWire x 10)*(atWire x 1207) :=
  wireStep x (by decide) (show patch archiveAt 1208=.mul 10 1207 from rfl) ⟨by decide,by decide⟩
private theorem e1209 (x : Fin 84→Rat) : (atWire x 1209)=(atWire x 150)+(atWire x 1208) :=
  wireStep x (by decide) (show patch archiveAt 1209=.add 150 1208 from rfl) ⟨by decide,by decide⟩
private theorem e1246 (x : Fin 84→Rat) : (atWire x 1246)=(atWire x 1203)*(atWire x 1209) :=
  wireStep x (by decide) (show patch archiveAt 1246=.mul 1203 1209 from rfl) ⟨by decide,by decide⟩
private theorem e1247 (x : Fin 84→Rat) : (atWire x 1247)=(atWire x 85)*(atWire x 1206) :=
  wireStep x (by decide) (show patch archiveAt 1247=.mul 85 1206 from rfl) ⟨by decide,by decide⟩
private theorem e1248 (x : Fin 84→Rat) : (atWire x 1248)=(atWire x 155)*(atWire x 1247) :=
  wireStep x (by decide) (show patch archiveAt 1248=.mul 155 1247 from rfl) ⟨by decide,by decide⟩
private theorem e1249 (x : Fin 84→Rat) : (atWire x 1249)=(atWire x 1246)+(atWire x 1248) :=
  wireStep x (by decide) (show patch archiveAt 1249=.add 1246 1248 from rfl) ⟨by decide,by decide⟩
private theorem e1250 (x : Fin 84→Rat) : (atWire x 1250)=(atWire x 155)*(atWire x 1203) :=
  wireStep x (by decide) (show patch archiveAt 1250=.mul 155 1203 from rfl) ⟨by decide,by decide⟩
private theorem e1251 (x : Fin 84→Rat) : (atWire x 1251)=(atWire x 1206)*(atWire x 1209) :=
  wireStep x (by decide) (show patch archiveAt 1251=.mul 1206 1209 from rfl) ⟨by decide,by decide⟩
private theorem e1252 (x : Fin 84→Rat) : (atWire x 1252)=(atWire x 1250)+(atWire x 1251) :=
  wireStep x (by decide) (show patch archiveAt 1252=.add 1250 1251 from rfl) ⟨by decide,by decide⟩
private theorem e1254 (x : Fin 84→Rat) : (atWire x 1254)=(atWire x 1252)*(atWire x 1252) :=
  wireStep x (by decide) (show patch archiveAt 1254=.mul 1252 1252 from rfl) ⟨by decide,by decide⟩
private theorem e1255 (x : Fin 84→Rat) : (atWire x 1255)=(atWire x 84)+(atWire x 1254) :=
  wireStep x (by decide) (show patch archiveAt 1255=.add 84 1254 from rfl) ⟨by decide,by decide⟩
private theorem factor0 (x : Fin 84→Rat) : ((atWire x 1075),(atWire x 121))=sq (cell x 2,cell x 3) := by
  apply Prod.ext <;> simp only [sq,times,e1075,e1074,e1073,e121,e120,e114,e85,e2,e1] <;> grobner
private theorem factor1 (x : Fin 84→Rat) : ((atWire x 1118),(atWire x 190))=sq ((atWire x 182)*cell x 5,(atWire x 182)*cell x 6) := by
  apply Prod.ext <;> simp only [sq,times,e1118,e1117,e1116,e190,e189,e185,e184,e183,e85,e5,e4] <;> grobner
private theorem factor2 (x : Fin 84→Rat) : ((atWire x 1163),(atWire x 161))=sq (cell x 7,cell x 8) := by
  apply Prod.ext <;> simp only [sq,times,e1163,e1162,e1161,e161,e160,e156,e85,e7,e6] <;> grobner
private theorem factor3 (x : Fin 84→Rat) : ((atWire x 1209),(atWire x 155))=sq (cell x 10,cell x 11) := by
  apply Prod.ext <;> simp only [sq,times,e1209,e1208,e1207,e155,e154,e150,e85,e10,e9] <;> grobner
private theorem stage0 (x : Fin 84→Rat) : ((atWire x 1157),(atWire x 1160))=times ((atWire x 1075),(atWire x 121)) ((atWire x 1118),(atWire x 190)) := by
  apply Prod.ext <;> simp only [sq,times,e1160,e1159,e1158,e1157,e1156,e1155,e1077,e85] <;> grobner
private theorem stage1 (x : Fin 84→Rat) : ((atWire x 1203),(atWire x 1206))=times ((atWire x 1157),(atWire x 1160)) ((atWire x 1163),(atWire x 161)) := by
  apply Prod.ext <;> simp only [sq,times,e1206,e1205,e1204,e1203,e1202,e1201,e1200,e85] <;> grobner
private theorem stage2 (x : Fin 84→Rat) : ((atWire x 1249),(atWire x 1252))=times ((atWire x 1203),(atWire x 1206)) ((atWire x 1209),(atWire x 155)) := by
  apply Prod.ext <;> simp only [sq,times,e1252,e1251,e1250,e1249,e1248,e1247,e1246,e85] <;> grobner
theorem root_product (x : Fin 84→Rat) : ((atWire x 1249),(atWire x 1252))=times (times (times (sq (cell x 2,cell x 3)) (sq ((atWire x 182)*cell x 5,(atWire x 182)*cell x 6))) (sq (cell x 7,cell x 8))) (sq (cell x 10,cell x 11)) := by
  rw [stage2,stage1,stage0,factor0,factor1,factor2,factor3]
theorem root_scale (x : Fin 84→Rat) : (atWire x 182)=(5070054779947717629308371384521789480239396134271756906351118151050703599166632466437044672432923755120388312614740520104204175287618362020963:Rat) := e182 x
theorem slope_values (x : Fin 84→Rat) :
    slope x .first=cell x 13 ∧ slope x .second=(atWire x 1249)^2*cell x 13 ∧
    slope x .third=(1+(atWire x 1252)^2)^2*cell x 13 := by
  refine ⟨h12 x,slope1 x,?_⟩
  change atWire x 8902=_
  rw [slope2,e1255,e1254,h84];grobner
#print axioms root_product
#print axioms root_scale
#print axioms slope_values
end HeightSpecialization
