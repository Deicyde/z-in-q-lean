import ConstantDelta
import Polynomial80
import ProductWires
namespace EllipticHeight.Labels
open CircuitTransport StructuralReduction StructuralReduction.Transfer84
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate ProjectionFibres
open ProjectionFibres.Comparison ProjectionFibres.Actual
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
private theorem e1 (x : Fin 84→Rat) : atWire x 1=cell x 2 :=
  wireStep x (by decide) (show patch archiveAt 1=.var 2 from rfl) trivial
private theorem e2 (x : Fin 84→Rat) : atWire x 2=cell x 3 :=
  wireStep x (by decide) (show patch archiveAt 2=.var 3 from rfl) trivial
private theorem e3 (x : Fin 84→Rat) : atWire x 3=cell x 4 :=
  wireStep x (by decide) (show patch archiveAt 3=.var 4 from rfl) trivial
private theorem e4 (x : Fin 84→Rat) : atWire x 4=cell x 5 :=
  wireStep x (by decide) (show patch archiveAt 4=.var 5 from rfl) trivial
private theorem e5 (x : Fin 84→Rat) : atWire x 5=cell x 6 :=
  wireStep x (by decide) (show patch archiveAt 5=.var 6 from rfl) trivial
private theorem e6 (x : Fin 84→Rat) : atWire x 6=cell x 7 :=
  wireStep x (by decide) (show patch archiveAt 6=.var 7 from rfl) trivial
private theorem e7 (x : Fin 84→Rat) : atWire x 7=cell x 8 :=
  wireStep x (by decide) (show patch archiveAt 7=.var 8 from rfl) trivial
private theorem e8 (x : Fin 84→Rat) : atWire x 8=cell x 9 :=
  wireStep x (by decide) (show patch archiveAt 8=.var 9 from rfl) trivial
private theorem e9 (x : Fin 84→Rat) : atWire x 9=cell x 10 :=
  wireStep x (by decide) (show patch archiveAt 9=.var 10 from rfl) trivial
private theorem e10 (x : Fin 84→Rat) : atWire x 10=cell x 11 :=
  wireStep x (by decide) (show patch archiveAt 10=.var 11 from rfl) trivial
private theorem e11 (x : Fin 84→Rat) : atWire x 11=cell x 12 :=
  wireStep x (by decide) (show patch archiveAt 11=.var 12 from rfl) trivial
private theorem e16 (x : Fin 84→Rat) : atWire x 16=cell x 17 :=
  wireStep x (by decide) (show patch archiveAt 16=.var 17 from rfl) trivial
private theorem e85 (x : Fin 84→Rat) : atWire x 85=(2:Rat) :=
  wireStep x (by decide) (show patch archiveAt 85=.int 2 from rfl) trivial
private theorem e98 (x : Fin 84→Rat) : atWire x 98=(-1:Rat) :=
  wireStep x (by decide) (show patch archiveAt 98=.int (-1) from rfl) trivial
private theorem e114 (x : Fin 84→Rat) : atWire x 114=atWire x 1*atWire x 1 :=
  wireStep x (by decide) (show patch archiveAt 114=.mul 1 1 from rfl) ⟨by decide,by decide⟩
private theorem e115 (x : Fin 84→Rat) : atWire x 115=atWire x 2*atWire x 2 :=
  wireStep x (by decide) (show patch archiveAt 115=.mul 2 2 from rfl) ⟨by decide,by decide⟩
private theorem e116 (x : Fin 84→Rat) : atWire x 116=atWire x 85*atWire x 115 :=
  wireStep x (by decide) (show patch archiveAt 116=.mul 85 115 from rfl) ⟨by decide,by decide⟩
private theorem e117 (x : Fin 84→Rat) : atWire x 117=atWire x 114+atWire x 116 :=
  wireStep x (by decide) (show patch archiveAt 117=.add 114 116 from rfl) ⟨by decide,by decide⟩
private theorem e118 (x : Fin 84→Rat) : atWire x 118=(11:Rat) :=
  wireStep x (by decide) (show patch archiveAt 118=.int 11 from rfl) trivial
private theorem e120 (x : Fin 84→Rat) : atWire x 120=atWire x 1*atWire x 2 :=
  wireStep x (by decide) (show patch archiveAt 120=.mul 1 2 from rfl) ⟨by decide,by decide⟩
private theorem e121 (x : Fin 84→Rat) : atWire x 121=atWire x 120+atWire x 120 :=
  wireStep x (by decide) (show patch archiveAt 121=.add 120 120 from rfl) ⟨by decide,by decide⟩
private theorem e122 (x : Fin 84→Rat) : atWire x 122=atWire x 117*atWire x 121 :=
  wireStep x (by decide) (show patch archiveAt 122=.mul 117 121 from rfl) ⟨by decide,by decide⟩
private theorem e123 (x : Fin 84→Rat) : atWire x 123=atWire x 122+atWire x 122 :=
  wireStep x (by decide) (show patch archiveAt 123=.add 122 122 from rfl) ⟨by decide,by decide⟩
private theorem e124 (x : Fin 84→Rat) : atWire x 124=atWire x 118*atWire x 123 :=
  wireStep x (by decide) (show patch archiveAt 124=.mul 118 123 from rfl) ⟨by decide,by decide⟩
private theorem e125 (x : Fin 84→Rat) : atWire x 125=(6:Rat) :=
  wireStep x (by decide) (show patch archiveAt 125=.int 6 from rfl) trivial
private theorem e126 (x : Fin 84→Rat) : atWire x 126=atWire x 117*atWire x 117 :=
  wireStep x (by decide) (show patch archiveAt 126=.mul 117 117 from rfl) ⟨by decide,by decide⟩
private theorem e127 (x : Fin 84→Rat) : atWire x 127=atWire x 121*atWire x 121 :=
  wireStep x (by decide) (show patch archiveAt 127=.mul 121 121 from rfl) ⟨by decide,by decide⟩
private theorem e128 (x : Fin 84→Rat) : atWire x 128=atWire x 85*atWire x 127 :=
  wireStep x (by decide) (show patch archiveAt 128=.mul 85 127 from rfl) ⟨by decide,by decide⟩
private theorem e129 (x : Fin 84→Rat) : atWire x 129=atWire x 126+atWire x 128 :=
  wireStep x (by decide) (show patch archiveAt 129=.add 126 128 from rfl) ⟨by decide,by decide⟩
private theorem e130 (x : Fin 84→Rat) : atWire x 130=atWire x 125*atWire x 129 :=
  wireStep x (by decide) (show patch archiveAt 130=.mul 125 129 from rfl) ⟨by decide,by decide⟩
private theorem e131 (x : Fin 84→Rat) : atWire x 131=atWire x 124+atWire x 130 :=
  wireStep x (by decide) (show patch archiveAt 131=.add 124 130 from rfl) ⟨by decide,by decide⟩
private theorem e132 (x : Fin 84→Rat) : atWire x 132=atWire x 3*atWire x 131 :=
  wireStep x (by decide) (show patch archiveAt 132=.mul 3 131 from rfl) ⟨by decide,by decide⟩
private theorem e133 (x : Fin 84→Rat) : atWire x 133=atWire x 132*atWire x 132 :=
  wireStep x (by decide) (show patch archiveAt 133=.mul 132 132 from rfl) ⟨by decide,by decide⟩
private theorem e134 (x : Fin 84→Rat) : atWire x 134=atWire x 98*atWire x 133 :=
  wireStep x (by decide) (show patch archiveAt 134=.mul 98 133 from rfl) ⟨by decide,by decide⟩
private theorem e135 (x : Fin 84→Rat) : atWire x 135=atWire x 118*atWire x 129 :=
  wireStep x (by decide) (show patch archiveAt 135=.mul 118 129 from rfl) ⟨by decide,by decide⟩
private theorem e136 (x : Fin 84→Rat) : atWire x 136=atWire x 123*atWire x 125 :=
  wireStep x (by decide) (show patch archiveAt 136=.mul 123 125 from rfl) ⟨by decide,by decide⟩
private theorem e137 (x : Fin 84→Rat) : atWire x 137=atWire x 85*atWire x 136 :=
  wireStep x (by decide) (show patch archiveAt 137=.mul 85 136 from rfl) ⟨by decide,by decide⟩
private theorem e138 (x : Fin 84→Rat) : atWire x 138=atWire x 135+atWire x 137 :=
  wireStep x (by decide) (show patch archiveAt 138=.add 135 137 from rfl) ⟨by decide,by decide⟩
private theorem e139 (x : Fin 84→Rat) : atWire x 139=(-49:Rat) :=
  wireStep x (by decide) (show patch archiveAt 139=.int (-49) from rfl) trivial
private theorem e140 (x : Fin 84→Rat) : atWire x 140=atWire x 138+atWire x 139 :=
  wireStep x (by decide) (show patch archiveAt 140=.add 138 139 from rfl) ⟨by decide,by decide⟩
private theorem e141 (x : Fin 84→Rat) : atWire x 141=(98:Rat) :=
  wireStep x (by decide) (show patch archiveAt 141=.int 98 from rfl) trivial
private theorem e142 (x : Fin 84→Rat) : atWire x 142=atWire x 140*atWire x 141 :=
  wireStep x (by decide) (show patch archiveAt 142=.mul 140 141 from rfl) ⟨by decide,by decide⟩
private theorem e143 (x : Fin 84→Rat) : atWire x 143=atWire x 134+atWire x 142 :=
  wireStep x (by decide) (show patch archiveAt 143=.add 134 142 from rfl) ⟨by decide,by decide⟩
private theorem e144 (x : Fin 84→Rat) : atWire x 144=atWire x 3*atWire x 143 :=
  wireStep x (by decide) (show patch archiveAt 144=.mul 3 143 from rfl) ⟨by decide,by decide⟩
private theorem e150 (x : Fin 84→Rat) : atWire x 150=atWire x 9*atWire x 9 :=
  wireStep x (by decide) (show patch archiveAt 150=.mul 9 9 from rfl) ⟨by decide,by decide⟩
private theorem e151 (x : Fin 84→Rat) : atWire x 151=atWire x 10*atWire x 10 :=
  wireStep x (by decide) (show patch archiveAt 151=.mul 10 10 from rfl) ⟨by decide,by decide⟩
private theorem e152 (x : Fin 84→Rat) : atWire x 152=atWire x 85*atWire x 151 :=
  wireStep x (by decide) (show patch archiveAt 152=.mul 85 151 from rfl) ⟨by decide,by decide⟩
private theorem e153 (x : Fin 84→Rat) : atWire x 153=atWire x 150+atWire x 152 :=
  wireStep x (by decide) (show patch archiveAt 153=.add 150 152 from rfl) ⟨by decide,by decide⟩
private theorem e154 (x : Fin 84→Rat) : atWire x 154=atWire x 9*atWire x 10 :=
  wireStep x (by decide) (show patch archiveAt 154=.mul 9 10 from rfl) ⟨by decide,by decide⟩
private theorem e155 (x : Fin 84→Rat) : atWire x 155=atWire x 154+atWire x 154 :=
  wireStep x (by decide) (show patch archiveAt 155=.add 154 154 from rfl) ⟨by decide,by decide⟩
private theorem e156 (x : Fin 84→Rat) : atWire x 156=atWire x 6*atWire x 6 :=
  wireStep x (by decide) (show patch archiveAt 156=.mul 6 6 from rfl) ⟨by decide,by decide⟩
private theorem e157 (x : Fin 84→Rat) : atWire x 157=atWire x 7*atWire x 7 :=
  wireStep x (by decide) (show patch archiveAt 157=.mul 7 7 from rfl) ⟨by decide,by decide⟩
private theorem e158 (x : Fin 84→Rat) : atWire x 158=atWire x 85*atWire x 157 :=
  wireStep x (by decide) (show patch archiveAt 158=.mul 85 157 from rfl) ⟨by decide,by decide⟩
private theorem e159 (x : Fin 84→Rat) : atWire x 159=atWire x 156+atWire x 158 :=
  wireStep x (by decide) (show patch archiveAt 159=.add 156 158 from rfl) ⟨by decide,by decide⟩
private theorem e160 (x : Fin 84→Rat) : atWire x 160=atWire x 6*atWire x 7 :=
  wireStep x (by decide) (show patch archiveAt 160=.mul 6 7 from rfl) ⟨by decide,by decide⟩
private theorem e161 (x : Fin 84→Rat) : atWire x 161=atWire x 160+atWire x 160 :=
  wireStep x (by decide) (show patch archiveAt 161=.add 160 160 from rfl) ⟨by decide,by decide⟩
private theorem e162 (x : Fin 84→Rat) : atWire x 162=atWire x 159*atWire x 161 :=
  wireStep x (by decide) (show patch archiveAt 162=.mul 159 161 from rfl) ⟨by decide,by decide⟩
private theorem e163 (x : Fin 84→Rat) : atWire x 163=atWire x 162+atWire x 162 :=
  wireStep x (by decide) (show patch archiveAt 163=.add 162 162 from rfl) ⟨by decide,by decide⟩
private theorem e164 (x : Fin 84→Rat) : atWire x 164=atWire x 118*atWire x 163 :=
  wireStep x (by decide) (show patch archiveAt 164=.mul 118 163 from rfl) ⟨by decide,by decide⟩
private theorem e165 (x : Fin 84→Rat) : atWire x 165=atWire x 159*atWire x 159 :=
  wireStep x (by decide) (show patch archiveAt 165=.mul 159 159 from rfl) ⟨by decide,by decide⟩
private theorem e166 (x : Fin 84→Rat) : atWire x 166=atWire x 161*atWire x 161 :=
  wireStep x (by decide) (show patch archiveAt 166=.mul 161 161 from rfl) ⟨by decide,by decide⟩
private theorem e167 (x : Fin 84→Rat) : atWire x 167=atWire x 85*atWire x 166 :=
  wireStep x (by decide) (show patch archiveAt 167=.mul 85 166 from rfl) ⟨by decide,by decide⟩
private theorem e168 (x : Fin 84→Rat) : atWire x 168=atWire x 165+atWire x 167 :=
  wireStep x (by decide) (show patch archiveAt 168=.add 165 167 from rfl) ⟨by decide,by decide⟩
private theorem e169 (x : Fin 84→Rat) : atWire x 169=atWire x 125*atWire x 168 :=
  wireStep x (by decide) (show patch archiveAt 169=.mul 125 168 from rfl) ⟨by decide,by decide⟩
private theorem e170 (x : Fin 84→Rat) : atWire x 170=atWire x 164+atWire x 169 :=
  wireStep x (by decide) (show patch archiveAt 170=.add 164 169 from rfl) ⟨by decide,by decide⟩
private theorem e171 (x : Fin 84→Rat) : atWire x 171=atWire x 8*atWire x 170 :=
  wireStep x (by decide) (show patch archiveAt 171=.mul 8 170 from rfl) ⟨by decide,by decide⟩
private theorem e172 (x : Fin 84→Rat) : atWire x 172=atWire x 171*atWire x 171 :=
  wireStep x (by decide) (show patch archiveAt 172=.mul 171 171 from rfl) ⟨by decide,by decide⟩
private theorem e173 (x : Fin 84→Rat) : atWire x 173=atWire x 98*atWire x 172 :=
  wireStep x (by decide) (show patch archiveAt 173=.mul 98 172 from rfl) ⟨by decide,by decide⟩
private theorem e174 (x : Fin 84→Rat) : atWire x 174=atWire x 118*atWire x 168 :=
  wireStep x (by decide) (show patch archiveAt 174=.mul 118 168 from rfl) ⟨by decide,by decide⟩
private theorem e175 (x : Fin 84→Rat) : atWire x 175=atWire x 125*atWire x 163 :=
  wireStep x (by decide) (show patch archiveAt 175=.mul 125 163 from rfl) ⟨by decide,by decide⟩
private theorem e176 (x : Fin 84→Rat) : atWire x 176=atWire x 85*atWire x 175 :=
  wireStep x (by decide) (show patch archiveAt 176=.mul 85 175 from rfl) ⟨by decide,by decide⟩
private theorem e177 (x : Fin 84→Rat) : atWire x 177=atWire x 174+atWire x 176 :=
  wireStep x (by decide) (show patch archiveAt 177=.add 174 176 from rfl) ⟨by decide,by decide⟩
private theorem e178 (x : Fin 84→Rat) : atWire x 178=atWire x 139+atWire x 177 :=
  wireStep x (by decide) (show patch archiveAt 178=.add 139 177 from rfl) ⟨by decide,by decide⟩
private theorem e179 (x : Fin 84→Rat) : atWire x 179=atWire x 141*atWire x 178 :=
  wireStep x (by decide) (show patch archiveAt 179=.mul 141 178 from rfl) ⟨by decide,by decide⟩
private theorem e180 (x : Fin 84→Rat) : atWire x 180=atWire x 173+atWire x 179 :=
  wireStep x (by decide) (show patch archiveAt 180=.add 173 179 from rfl) ⟨by decide,by decide⟩
private theorem e181 (x : Fin 84→Rat) : atWire x 181=atWire x 8*atWire x 180 :=
  wireStep x (by decide) (show patch archiveAt 181=.mul 8 180 from rfl) ⟨by decide,by decide⟩
private theorem e183 (x : Fin 84→Rat) : atWire x 183=atWire x 4*atWire x 182 :=
  wireStep x (by decide) (show patch archiveAt 183=.mul 4 182 from rfl) ⟨by decide,by decide⟩
private theorem e184 (x : Fin 84→Rat) : atWire x 184=atWire x 183*atWire x 183 :=
  wireStep x (by decide) (show patch archiveAt 184=.mul 183 183 from rfl) ⟨by decide,by decide⟩
private theorem e185 (x : Fin 84→Rat) : atWire x 185=atWire x 5*atWire x 182 :=
  wireStep x (by decide) (show patch archiveAt 185=.mul 5 182 from rfl) ⟨by decide,by decide⟩
private theorem e186 (x : Fin 84→Rat) : atWire x 186=atWire x 185*atWire x 185 :=
  wireStep x (by decide) (show patch archiveAt 186=.mul 185 185 from rfl) ⟨by decide,by decide⟩
private theorem e187 (x : Fin 84→Rat) : atWire x 187=atWire x 85*atWire x 186 :=
  wireStep x (by decide) (show patch archiveAt 187=.mul 85 186 from rfl) ⟨by decide,by decide⟩
private theorem e188 (x : Fin 84→Rat) : atWire x 188=atWire x 184+atWire x 187 :=
  wireStep x (by decide) (show patch archiveAt 188=.add 184 187 from rfl) ⟨by decide,by decide⟩
private theorem e189 (x : Fin 84→Rat) : atWire x 189=atWire x 183*atWire x 185 :=
  wireStep x (by decide) (show patch archiveAt 189=.mul 183 185 from rfl) ⟨by decide,by decide⟩
private theorem e190 (x : Fin 84→Rat) : atWire x 190=atWire x 189+atWire x 189 :=
  wireStep x (by decide) (show patch archiveAt 190=.add 189 189 from rfl) ⟨by decide,by decide⟩
private theorem e191 (x : Fin 84→Rat) : atWire x 191=atWire x 188*atWire x 190 :=
  wireStep x (by decide) (show patch archiveAt 191=.mul 188 190 from rfl) ⟨by decide,by decide⟩
private theorem e192 (x : Fin 84→Rat) : atWire x 192=atWire x 191+atWire x 191 :=
  wireStep x (by decide) (show patch archiveAt 192=.add 191 191 from rfl) ⟨by decide,by decide⟩
private theorem e193 (x : Fin 84→Rat) : atWire x 193=atWire x 118*atWire x 192 :=
  wireStep x (by decide) (show patch archiveAt 193=.mul 118 192 from rfl) ⟨by decide,by decide⟩
private theorem e194 (x : Fin 84→Rat) : atWire x 194=atWire x 188*atWire x 188 :=
  wireStep x (by decide) (show patch archiveAt 194=.mul 188 188 from rfl) ⟨by decide,by decide⟩
private theorem e195 (x : Fin 84→Rat) : atWire x 195=atWire x 190*atWire x 190 :=
  wireStep x (by decide) (show patch archiveAt 195=.mul 190 190 from rfl) ⟨by decide,by decide⟩
private theorem e196 (x : Fin 84→Rat) : atWire x 196=atWire x 85*atWire x 195 :=
  wireStep x (by decide) (show patch archiveAt 196=.mul 85 195 from rfl) ⟨by decide,by decide⟩
private theorem e197 (x : Fin 84→Rat) : atWire x 197=atWire x 194+atWire x 196 :=
  wireStep x (by decide) (show patch archiveAt 197=.add 194 196 from rfl) ⟨by decide,by decide⟩
private theorem e198 (x : Fin 84→Rat) : atWire x 198=atWire x 125*atWire x 197 :=
  wireStep x (by decide) (show patch archiveAt 198=.mul 125 197 from rfl) ⟨by decide,by decide⟩
private theorem e199 (x : Fin 84→Rat) : atWire x 199=atWire x 193+atWire x 198 :=
  wireStep x (by decide) (show patch archiveAt 199=.add 193 198 from rfl) ⟨by decide,by decide⟩
private theorem e200 (x : Fin 84→Rat) : atWire x 200=atWire x 16*atWire x 199 :=
  wireStep x (by decide) (show patch archiveAt 200=.mul 16 199 from rfl) ⟨by decide,by decide⟩
private theorem e201 (x : Fin 84→Rat) : atWire x 201=atWire x 200*atWire x 200 :=
  wireStep x (by decide) (show patch archiveAt 201=.mul 200 200 from rfl) ⟨by decide,by decide⟩
private theorem e202 (x : Fin 84→Rat) : atWire x 202=atWire x 98*atWire x 201 :=
  wireStep x (by decide) (show patch archiveAt 202=.mul 98 201 from rfl) ⟨by decide,by decide⟩
private theorem e203 (x : Fin 84→Rat) : atWire x 203=atWire x 118*atWire x 197 :=
  wireStep x (by decide) (show patch archiveAt 203=.mul 118 197 from rfl) ⟨by decide,by decide⟩
private theorem e204 (x : Fin 84→Rat) : atWire x 204=atWire x 125*atWire x 192 :=
  wireStep x (by decide) (show patch archiveAt 204=.mul 125 192 from rfl) ⟨by decide,by decide⟩
private theorem e205 (x : Fin 84→Rat) : atWire x 205=atWire x 85*atWire x 204 :=
  wireStep x (by decide) (show patch archiveAt 205=.mul 85 204 from rfl) ⟨by decide,by decide⟩
private theorem e206 (x : Fin 84→Rat) : atWire x 206=atWire x 203+atWire x 205 :=
  wireStep x (by decide) (show patch archiveAt 206=.add 203 205 from rfl) ⟨by decide,by decide⟩
private theorem e207 (x : Fin 84→Rat) : atWire x 207=atWire x 139+atWire x 206 :=
  wireStep x (by decide) (show patch archiveAt 207=.add 139 206 from rfl) ⟨by decide,by decide⟩
private theorem e208 (x : Fin 84→Rat) : atWire x 208=atWire x 141*atWire x 207 :=
  wireStep x (by decide) (show patch archiveAt 208=.mul 141 207 from rfl) ⟨by decide,by decide⟩
private theorem e209 (x : Fin 84→Rat) : atWire x 209=atWire x 202+atWire x 208 :=
  wireStep x (by decide) (show patch archiveAt 209=.add 202 208 from rfl) ⟨by decide,by decide⟩
private theorem e210 (x : Fin 84→Rat) : atWire x 210=atWire x 16*atWire x 209 :=
  wireStep x (by decide) (show patch archiveAt 210=.mul 16 209 from rfl) ⟨by decide,by decide⟩
private theorem e220 (x : Fin 84→Rat) : atWire x 220=atWire x 153*atWire x 155 :=
  wireStep x (by decide) (show patch archiveAt 220=.mul 153 155 from rfl) ⟨by decide,by decide⟩
private theorem e221 (x : Fin 84→Rat) : atWire x 221=atWire x 220+atWire x 220 :=
  wireStep x (by decide) (show patch archiveAt 221=.add 220 220 from rfl) ⟨by decide,by decide⟩
private theorem e222 (x : Fin 84→Rat) : atWire x 222=atWire x 118*atWire x 221 :=
  wireStep x (by decide) (show patch archiveAt 222=.mul 118 221 from rfl) ⟨by decide,by decide⟩
private theorem e223 (x : Fin 84→Rat) : atWire x 223=atWire x 153*atWire x 153 :=
  wireStep x (by decide) (show patch archiveAt 223=.mul 153 153 from rfl) ⟨by decide,by decide⟩
private theorem e224 (x : Fin 84→Rat) : atWire x 224=atWire x 155*atWire x 155 :=
  wireStep x (by decide) (show patch archiveAt 224=.mul 155 155 from rfl) ⟨by decide,by decide⟩
private theorem e225 (x : Fin 84→Rat) : atWire x 225=atWire x 85*atWire x 224 :=
  wireStep x (by decide) (show patch archiveAt 225=.mul 85 224 from rfl) ⟨by decide,by decide⟩
private theorem e226 (x : Fin 84→Rat) : atWire x 226=atWire x 223+atWire x 225 :=
  wireStep x (by decide) (show patch archiveAt 226=.add 223 225 from rfl) ⟨by decide,by decide⟩
private theorem e227 (x : Fin 84→Rat) : atWire x 227=atWire x 125*atWire x 226 :=
  wireStep x (by decide) (show patch archiveAt 227=.mul 125 226 from rfl) ⟨by decide,by decide⟩
private theorem e228 (x : Fin 84→Rat) : atWire x 228=atWire x 222+atWire x 227 :=
  wireStep x (by decide) (show patch archiveAt 228=.add 222 227 from rfl) ⟨by decide,by decide⟩
private theorem e229 (x : Fin 84→Rat) : atWire x 229=atWire x 11*atWire x 228 :=
  wireStep x (by decide) (show patch archiveAt 229=.mul 11 228 from rfl) ⟨by decide,by decide⟩
private theorem e230 (x : Fin 84→Rat) : atWire x 230=atWire x 229*atWire x 229 :=
  wireStep x (by decide) (show patch archiveAt 230=.mul 229 229 from rfl) ⟨by decide,by decide⟩
private theorem e231 (x : Fin 84→Rat) : atWire x 231=atWire x 98*atWire x 230 :=
  wireStep x (by decide) (show patch archiveAt 231=.mul 98 230 from rfl) ⟨by decide,by decide⟩
private theorem e232 (x : Fin 84→Rat) : atWire x 232=atWire x 118*atWire x 226 :=
  wireStep x (by decide) (show patch archiveAt 232=.mul 118 226 from rfl) ⟨by decide,by decide⟩
private theorem e233 (x : Fin 84→Rat) : atWire x 233=atWire x 125*atWire x 221 :=
  wireStep x (by decide) (show patch archiveAt 233=.mul 125 221 from rfl) ⟨by decide,by decide⟩
private theorem e234 (x : Fin 84→Rat) : atWire x 234=atWire x 85*atWire x 233 :=
  wireStep x (by decide) (show patch archiveAt 234=.mul 85 233 from rfl) ⟨by decide,by decide⟩
private theorem e235 (x : Fin 84→Rat) : atWire x 235=atWire x 232+atWire x 234 :=
  wireStep x (by decide) (show patch archiveAt 235=.add 232 234 from rfl) ⟨by decide,by decide⟩
private theorem e236 (x : Fin 84→Rat) : atWire x 236=atWire x 139+atWire x 235 :=
  wireStep x (by decide) (show patch archiveAt 236=.add 139 235 from rfl) ⟨by decide,by decide⟩
private theorem e237 (x : Fin 84→Rat) : atWire x 237=atWire x 141*atWire x 236 :=
  wireStep x (by decide) (show patch archiveAt 237=.mul 141 236 from rfl) ⟨by decide,by decide⟩
private theorem e238 (x : Fin 84→Rat) : atWire x 238=atWire x 231+atWire x 237 :=
  wireStep x (by decide) (show patch archiveAt 238=.add 231 237 from rfl) ⟨by decide,by decide⟩
private theorem e239 (x : Fin 84→Rat) : atWire x 239=atWire x 11*atWire x 238 :=
  wireStep x (by decide) (show patch archiveAt 239=.mul 11 238 from rfl) ⟨by decide,by decide⟩
private theorem e241 (x : Fin 84→Rat) : atWire x 241=(4802:Rat) :=
  wireStep x (by decide) (show patch archiveAt 241=.int 4802 from rfl) trivial
private theorem e448 (x : Fin 84→Rat) : atWire x 448=atWire x 11*atWire x 239 :=
  wireStep x (by decide) (show patch archiveAt 448=.mul 11 239 from rfl) ⟨by decide,by decide⟩
private theorem e449 (x : Fin 84→Rat) : atWire x 449=atWire x 98*atWire x 448 :=
  wireStep x (by decide) (show patch archiveAt 449=.mul 98 448 from rfl) ⟨by decide,by decide⟩
private theorem e450 (x : Fin 84→Rat) : atWire x 450=atWire x 241+atWire x 449 :=
  wireStep x (by decide) (show patch archiveAt 450=.add 241 449 from rfl) ⟨by decide,by decide⟩
private theorem e451 (x : Fin 84→Rat) : atWire x 451=atWire x 85*atWire x 450 :=
  wireStep x (by decide) (show patch archiveAt 451=.mul 85 450 from rfl) ⟨by decide,by decide⟩
private theorem e452 (x : Fin 84→Rat) : atWire x 452=atWire x 8*atWire x 181 :=
  wireStep x (by decide) (show patch archiveAt 452=.mul 8 181 from rfl) ⟨by decide,by decide⟩
private theorem e453 (x : Fin 84→Rat) : atWire x 453=atWire x 98*atWire x 452 :=
  wireStep x (by decide) (show patch archiveAt 453=.mul 98 452 from rfl) ⟨by decide,by decide⟩
private theorem e454 (x : Fin 84→Rat) : atWire x 454=atWire x 241+atWire x 453 :=
  wireStep x (by decide) (show patch archiveAt 454=.add 241 453 from rfl) ⟨by decide,by decide⟩
private theorem e455 (x : Fin 84→Rat) : atWire x 455=atWire x 85*atWire x 454 :=
  wireStep x (by decide) (show patch archiveAt 455=.mul 85 454 from rfl) ⟨by decide,by decide⟩
private theorem e456 (x : Fin 84→Rat) : atWire x 456=atWire x 16*atWire x 210 :=
  wireStep x (by decide) (show patch archiveAt 456=.mul 16 210 from rfl) ⟨by decide,by decide⟩
private theorem e457 (x : Fin 84→Rat) : atWire x 457=atWire x 98*atWire x 456 :=
  wireStep x (by decide) (show patch archiveAt 457=.mul 98 456 from rfl) ⟨by decide,by decide⟩
private theorem e458 (x : Fin 84→Rat) : atWire x 458=atWire x 241+atWire x 457 :=
  wireStep x (by decide) (show patch archiveAt 458=.add 241 457 from rfl) ⟨by decide,by decide⟩
private theorem e459 (x : Fin 84→Rat) : atWire x 459=atWire x 85*atWire x 458 :=
  wireStep x (by decide) (show patch archiveAt 459=.mul 85 458 from rfl) ⟨by decide,by decide⟩
private theorem e460 (x : Fin 84→Rat) : atWire x 460=atWire x 3*atWire x 144 :=
  wireStep x (by decide) (show patch archiveAt 460=.mul 3 144 from rfl) ⟨by decide,by decide⟩
private theorem e461 (x : Fin 84→Rat) : atWire x 461=atWire x 98*atWire x 460 :=
  wireStep x (by decide) (show patch archiveAt 461=.mul 98 460 from rfl) ⟨by decide,by decide⟩
private theorem e462 (x : Fin 84→Rat) : atWire x 462=atWire x 241+atWire x 461 :=
  wireStep x (by decide) (show patch archiveAt 462=.add 241 461 from rfl) ⟨by decide,by decide⟩
private theorem e463 (x : Fin 84→Rat) : atWire x 463=atWire x 85*atWire x 462 :=
  wireStep x (by decide) (show patch archiveAt 463=.mul 85 462 from rfl) ⟨by decide,by decide⟩
private theorem r463 (x : Fin 84→Rat) : atWire x 463 =
    4802*equation (deltaTarget (cell x 2,cell x 3)) (cell x 4) := by
  simp only [e463,e462,e461,e460,e241,e144,e143,e142,e141,e140,e139,e138,e137,e136,e135,e134,e133,e132,e131,e130,e129,e128,e127,e126,e125,e124,e123,e122,e121,e120,e118,e117,e116,e115,e114,e98,e85,e3,e2,e1,equation,deltaTarget,divDelta,sub,sq,times,PhysicalProjection.Comparison.one]
  grobner
private theorem r459 (x : Fin 84→Rat) : atWire x 459 =
    4802*equation (deltaTarget (atWire x 182*cell x 5,atWire x 182*cell x 6)) (cell x 17) := by
  simp only [e459,e458,e457,e456,e241,e210,e209,e208,e207,e206,e205,e204,e203,e202,e201,e200,e199,e198,e197,e196,e195,e194,e193,e192,e191,e190,e189,e188,e187,e186,e185,e184,e183,e141,e139,e125,e118,e98,e85,e16,e5,e4,equation,deltaTarget,divDelta,sub,sq,times,PhysicalProjection.Comparison.one]
  grobner
private theorem r455 (x : Fin 84→Rat) : atWire x 455 =
    4802*equation (deltaTarget (cell x 7,cell x 8)) (cell x 9) := by
  simp only [e455,e454,e453,e452,e241,e181,e180,e179,e178,e177,e176,e175,e174,e173,e172,e171,e170,e169,e168,e167,e166,e165,e164,e163,e162,e161,e160,e159,e158,e157,e156,e141,e139,e125,e118,e98,e85,e8,e7,e6,equation,deltaTarget,divDelta,sub,sq,times,PhysicalProjection.Comparison.one]
  grobner
private theorem r451 (x : Fin 84→Rat) : atWire x 451 =
    4802*equation (deltaTarget (cell x 10,cell x 11)) (cell x 12) := by
  simp only [e451,e450,e449,e448,e241,e239,e238,e237,e236,e235,e234,e233,e232,e231,e230,e229,e228,e227,e226,e225,e224,e223,e222,e221,e220,e155,e154,e153,e152,e151,e150,e141,e139,e125,e118,e98,e85,e11,e10,e9,equation,deltaTarget,divDelta,sub,sq,times,PhysicalProjection.Comparison.one]
  grobner
def rootH (x : Fin 84→Rat) (i : Fin 4) : Q2 :=
  if i=0 then (cell x 2,cell x 3) else if i=1 then (atWire x 182*cell x 5,atWire x 182*cell x 6) else if i=2 then (cell x 7,cell x 8) else (cell x 10,cell x 11)
def rootU (x : Fin 84→Rat) (i : Fin 4) : Rat :=
  if i=0 then cell x 4 else if i=1 then cell x 17 else if i=2 then cell x 9 else cell x 12
def rootJ (x : Fin 84→Rat) (i : Fin 4) : Q2 :=
  times delta (ordinate (deltaTarget (rootH x i)) (rootU x i))
theorem chart_equations {x : Fin 84→Rat} (z : output false x=0) (i : Fin 4) :
    equation (deltaTarget (rootH x i)) (rootU x i)=0 := by
  have each {r : Nat} (mem : r∈Output.wireList) := signed_zero x false (by simp) z r mem
  have index : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases index with rfl|rfl|rfl|rfl
  · have s:=each (r:=463) (by decide)
    rw [r463] at s
    change equation _ _=0
    simpa only [rootH,rootU,if_pos,if_neg] using
      (Rat.mul_eq_zero.mp s).resolve_left (by decide : (4802:Rat)≠0)
  · have s:=each (r:=459) (by decide)
    rw [r459] at s
    change equation _ _=0
    simpa only [rootH,rootU,if_pos,if_neg] using
      (Rat.mul_eq_zero.mp s).resolve_left (by decide : (4802:Rat)≠0)
  · have s:=each (r:=455) (by decide)
    rw [r455] at s
    change equation _ _=0
    simpa only [rootH,rootU,if_pos,if_neg] using
      (Rat.mul_eq_zero.mp s).resolve_left (by decide : (4802:Rat)≠0)
  · have s:=each (r:=451) (by decide)
    rw [r451] at s
    change equation _ _=0
    simpa only [rootH,rootU,if_pos,if_neg] using
      (Rat.mul_eq_zero.mp s).resolve_left (by decide : (4802:Rat)≠0)
theorem physical_root_charts (y : Fin 80→Rat) (zero : Binding.V y 9813=0) (i : Fin 4) :
    root (rootH (decoded y) i) (rootJ (decoded y) i) ∧
      rootH (decoded y) i≠(0,0) ∧ rootJ (decoded y) i≠(0,0) := by
  have z:=ordinary_decoded y ((Binding.ordinary_pointwise y).symm.trans zero)
  have eq:=chart_equations z i
  have both := (delta_pointwise _ (rootJ (decoded y) i) _).mpr ⟨eq,rfl⟩
  refine ⟨both.1,delta_scalar_nonzero eq,?_⟩
  intro bad; have unit:=both.2; rw [bad] at unit; dsimp [divDelta,times] at unit; grobner
#print axioms chart_equations
#print axioms physical_root_charts
end EllipticHeight.Labels
