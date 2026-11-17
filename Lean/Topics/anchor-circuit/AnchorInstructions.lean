import AnchorCoordinates
namespace AnchorCircuit
open CircuitTransport StructuralReduction StructuralReduction.Transfer84
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate
open ProjectionFibres.Comparison EllipticHeight.Labels
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def linearFactor (x : Fin 84 → Rat) : Rat := 307328 * atWire x 300

def firstProduct (x : Fin 84 → Rat) : Rat :=
  (cell x 10^2+2*cell x 11^2)*atWire x 399+8*cell x 10*cell x 11*atWire x 447

private theorem h0 (x : Fin 84 → Rat) : rootH x 0=(cell x 2,cell x 3) := rfl
private theorem h1 (x : Fin 84 → Rat) :
    rootH x 1=(atWire x 182*cell x 5,atWire x 182*cell x 6) := rfl
private theorem h2 (x : Fin 84 → Rat) : rootH x 2=(cell x 7,cell x 8) := rfl
private theorem h3 (x : Fin 84 → Rat) : rootH x 3=(cell x 10,cell x 11) := rfl
private theorem j1 (x : Fin 84 → Rat) :
    rootJ x 1=times delta (ordinate (deltaTarget (rootH x 1)) (cell x 17)) := rfl
private theorem e1 (x : Fin 84 → Rat) : atWire x 1 = cell x 2 := wireStep x (by decide) (show patch archiveAt 1=.var 2 from rfl) trivial

private theorem e2 (x : Fin 84 → Rat) : atWire x 2 = cell x 3 := wireStep x (by decide) (show patch archiveAt 2=.var 3 from rfl) trivial

private theorem e4 (x : Fin 84 → Rat) : atWire x 4 = cell x 5 := wireStep x (by decide) (show patch archiveAt 4=.var 5 from rfl) trivial

private theorem e5 (x : Fin 84 → Rat) : atWire x 5 = cell x 6 := wireStep x (by decide) (show patch archiveAt 5=.var 6 from rfl) trivial

private theorem e6 (x : Fin 84 → Rat) : atWire x 6 = cell x 7 := wireStep x (by decide) (show patch archiveAt 6=.var 7 from rfl) trivial

private theorem e7 (x : Fin 84 → Rat) : atWire x 7 = cell x 8 := wireStep x (by decide) (show patch archiveAt 7=.var 8 from rfl) trivial

private theorem e9 (x : Fin 84 → Rat) : atWire x 9 = cell x 10 := wireStep x (by decide) (show patch archiveAt 9=.var 10 from rfl) trivial

private theorem e10 (x : Fin 84 → Rat) : atWire x 10 = cell x 11 := wireStep x (by decide) (show patch archiveAt 10=.var 11 from rfl) trivial

private theorem e13 (x : Fin 84 → Rat) : atWire x 13 = cell x 14 := wireStep x (by decide) (show patch archiveAt 13=.var 14 from rfl) trivial

private theorem e14 (x : Fin 84 → Rat) : atWire x 14 = cell x 15 := wireStep x (by decide) (show patch archiveAt 14=.var 15 from rfl) trivial

private theorem e15 (x : Fin 84 → Rat) : atWire x 15 = cell x 16 := wireStep x (by decide) (show patch archiveAt 15=.var 16 from rfl) trivial

private theorem e16 (x : Fin 84 → Rat) : atWire x 16 = cell x 17 := wireStep x (by decide) (show patch archiveAt 16=.var 17 from rfl) trivial

private theorem e85 (x : Fin 84 → Rat) : atWire x 85 = (2:Rat) := wireStep x (by decide) (show patch archiveAt 85=.int (2) from rfl) trivial

private theorem e88 (x : Fin 84 → Rat) : atWire x 88 = (7:Rat) := wireStep x (by decide) (show patch archiveAt 88=.int (7) from rfl) trivial

private theorem e96 (x : Fin 84 → Rat) : atWire x 96 = (2401:Rat) := wireStep x (by decide) (show patch archiveAt 96=.int (2401) from rfl) trivial

private theorem e98 (x : Fin 84 → Rat) : atWire x 98 = (-1:Rat) := wireStep x (by decide) (show patch archiveAt 98=.int (-1) from rfl) trivial

private theorem e118 (x : Fin 84 → Rat) : atWire x 118 = (11:Rat) := wireStep x (by decide) (show patch archiveAt 118=.int (11) from rfl) trivial

private theorem e125 (x : Fin 84 → Rat) : atWire x 125 = (6:Rat) := wireStep x (by decide) (show patch archiveAt 125=.int (6) from rfl) trivial

private theorem e139 (x : Fin 84 → Rat) : atWire x 139 = (-49:Rat) := wireStep x (by decide) (show patch archiveAt 139=.int (-49) from rfl) trivial

private theorem e141 (x : Fin 84 → Rat) : atWire x 141 = (98:Rat) := wireStep x (by decide) (show patch archiveAt 141=.int (98) from rfl) trivial

private theorem e145 (x : Fin 84 → Rat) : atWire x 145 = (3:Rat) := wireStep x (by decide) (show patch archiveAt 145=.int (3) from rfl) trivial

private theorem e146 (x : Fin 84 → Rat) : atWire x 146 = (49:Rat) := wireStep x (by decide) (show patch archiveAt 146=.int (49) from rfl) trivial

private theorem e147 (x : Fin 84 → Rat) : atWire x 147 = (4:Rat) := wireStep x (by decide) (show patch archiveAt 147=.int (4) from rfl) trivial

private theorem e148 (x : Fin 84 → Rat) : atWire x 148 = (-2:Rat) := wireStep x (by decide) (show patch archiveAt 148=.int (-2) from rfl) trivial

private theorem e149 (x : Fin 84 → Rat) : atWire x 149 = (-8:Rat) := wireStep x (by decide) (show patch archiveAt 149=.int (-8) from rfl) trivial

private theorem e183 (x : Fin 84 → Rat) : atWire x 183 = atWire x 4 * atWire x 182 := wireStep x (by decide) (show patch archiveAt 183=.mul 4 182 from rfl) ⟨by decide,by decide⟩

private theorem e184 (x : Fin 84 → Rat) : atWire x 184 = atWire x 183 * atWire x 183 := wireStep x (by decide) (show patch archiveAt 184=.mul 183 183 from rfl) ⟨by decide,by decide⟩

private theorem e185 (x : Fin 84 → Rat) : atWire x 185 = atWire x 5 * atWire x 182 := wireStep x (by decide) (show patch archiveAt 185=.mul 5 182 from rfl) ⟨by decide,by decide⟩

private theorem e186 (x : Fin 84 → Rat) : atWire x 186 = atWire x 185 * atWire x 185 := wireStep x (by decide) (show patch archiveAt 186=.mul 185 185 from rfl) ⟨by decide,by decide⟩

private theorem e187 (x : Fin 84 → Rat) : atWire x 187 = atWire x 85 * atWire x 186 := wireStep x (by decide) (show patch archiveAt 187=.mul 85 186 from rfl) ⟨by decide,by decide⟩

private theorem e188 (x : Fin 84 → Rat) : atWire x 188 = atWire x 184 + atWire x 187 := wireStep x (by decide) (show patch archiveAt 188=.add 184 187 from rfl) ⟨by decide,by decide⟩

private theorem e189 (x : Fin 84 → Rat) : atWire x 189 = atWire x 183 * atWire x 185 := wireStep x (by decide) (show patch archiveAt 189=.mul 183 185 from rfl) ⟨by decide,by decide⟩

private theorem e190 (x : Fin 84 → Rat) : atWire x 190 = atWire x 189 + atWire x 189 := wireStep x (by decide) (show patch archiveAt 190=.add 189 189 from rfl) ⟨by decide,by decide⟩

private theorem e191 (x : Fin 84 → Rat) : atWire x 191 = atWire x 188 * atWire x 190 := wireStep x (by decide) (show patch archiveAt 191=.mul 188 190 from rfl) ⟨by decide,by decide⟩

private theorem e192 (x : Fin 84 → Rat) : atWire x 192 = atWire x 191 + atWire x 191 := wireStep x (by decide) (show patch archiveAt 192=.add 191 191 from rfl) ⟨by decide,by decide⟩

private theorem e193 (x : Fin 84 → Rat) : atWire x 193 = atWire x 118 * atWire x 192 := wireStep x (by decide) (show patch archiveAt 193=.mul 118 192 from rfl) ⟨by decide,by decide⟩

private theorem e194 (x : Fin 84 → Rat) : atWire x 194 = atWire x 188 * atWire x 188 := wireStep x (by decide) (show patch archiveAt 194=.mul 188 188 from rfl) ⟨by decide,by decide⟩

private theorem e195 (x : Fin 84 → Rat) : atWire x 195 = atWire x 190 * atWire x 190 := wireStep x (by decide) (show patch archiveAt 195=.mul 190 190 from rfl) ⟨by decide,by decide⟩

private theorem e196 (x : Fin 84 → Rat) : atWire x 196 = atWire x 85 * atWire x 195 := wireStep x (by decide) (show patch archiveAt 196=.mul 85 195 from rfl) ⟨by decide,by decide⟩

private theorem e197 (x : Fin 84 → Rat) : atWire x 197 = atWire x 194 + atWire x 196 := wireStep x (by decide) (show patch archiveAt 197=.add 194 196 from rfl) ⟨by decide,by decide⟩

private theorem e198 (x : Fin 84 → Rat) : atWire x 198 = atWire x 125 * atWire x 197 := wireStep x (by decide) (show patch archiveAt 198=.mul 125 197 from rfl) ⟨by decide,by decide⟩

private theorem e199 (x : Fin 84 → Rat) : atWire x 199 = atWire x 193 + atWire x 198 := wireStep x (by decide) (show patch archiveAt 199=.add 193 198 from rfl) ⟨by decide,by decide⟩

private theorem e200 (x : Fin 84 → Rat) : atWire x 200 = atWire x 16 * atWire x 199 := wireStep x (by decide) (show patch archiveAt 200=.mul 16 199 from rfl) ⟨by decide,by decide⟩

private theorem e201 (x : Fin 84 → Rat) : atWire x 201 = atWire x 200 * atWire x 200 := wireStep x (by decide) (show patch archiveAt 201=.mul 200 200 from rfl) ⟨by decide,by decide⟩

private theorem e202 (x : Fin 84 → Rat) : atWire x 202 = atWire x 98 * atWire x 201 := wireStep x (by decide) (show patch archiveAt 202=.mul 98 201 from rfl) ⟨by decide,by decide⟩

private theorem e203 (x : Fin 84 → Rat) : atWire x 203 = atWire x 118 * atWire x 197 := wireStep x (by decide) (show patch archiveAt 203=.mul 118 197 from rfl) ⟨by decide,by decide⟩

private theorem e204 (x : Fin 84 → Rat) : atWire x 204 = atWire x 125 * atWire x 192 := wireStep x (by decide) (show patch archiveAt 204=.mul 125 192 from rfl) ⟨by decide,by decide⟩

private theorem e205 (x : Fin 84 → Rat) : atWire x 205 = atWire x 85 * atWire x 204 := wireStep x (by decide) (show patch archiveAt 205=.mul 85 204 from rfl) ⟨by decide,by decide⟩

private theorem e206 (x : Fin 84 → Rat) : atWire x 206 = atWire x 203 + atWire x 205 := wireStep x (by decide) (show patch archiveAt 206=.add 203 205 from rfl) ⟨by decide,by decide⟩

private theorem e207 (x : Fin 84 → Rat) : atWire x 207 = atWire x 139 + atWire x 206 := wireStep x (by decide) (show patch archiveAt 207=.add 139 206 from rfl) ⟨by decide,by decide⟩

private theorem e208 (x : Fin 84 → Rat) : atWire x 208 = atWire x 141 * atWire x 207 := wireStep x (by decide) (show patch archiveAt 208=.mul 141 207 from rfl) ⟨by decide,by decide⟩

private theorem e209 (x : Fin 84 → Rat) : atWire x 209 = atWire x 202 + atWire x 208 := wireStep x (by decide) (show patch archiveAt 209=.add 202 208 from rfl) ⟨by decide,by decide⟩

private theorem e210 (x : Fin 84 → Rat) : atWire x 210 = atWire x 16 * atWire x 209 := wireStep x (by decide) (show patch archiveAt 210=.mul 16 209 from rfl) ⟨by decide,by decide⟩

private theorem e211 (x : Fin 84 → Rat) : atWire x 211 = atWire x 145 * atWire x 210 := wireStep x (by decide) (show patch archiveAt 211=.mul 145 210 from rfl) ⟨by decide,by decide⟩

private theorem e212 (x : Fin 84 → Rat) : atWire x 212 = atWire x 98 * atWire x 200 := wireStep x (by decide) (show patch archiveAt 212=.mul 98 200 from rfl) ⟨by decide,by decide⟩

private theorem e213 (x : Fin 84 → Rat) : atWire x 213 = atWire x 85 * atWire x 212 := wireStep x (by decide) (show patch archiveAt 213=.mul 85 212 from rfl) ⟨by decide,by decide⟩

private theorem e214 (x : Fin 84 → Rat) : atWire x 214 = atWire x 146 * atWire x 213 := wireStep x (by decide) (show patch archiveAt 214=.mul 146 213 from rfl) ⟨by decide,by decide⟩

private theorem e215 (x : Fin 84 → Rat) : atWire x 215 = atWire x 211 + atWire x 214 := wireStep x (by decide) (show patch archiveAt 215=.add 211 214 from rfl) ⟨by decide,by decide⟩

private theorem e216 (x : Fin 84 → Rat) : atWire x 216 = atWire x 98 * atWire x 210 := wireStep x (by decide) (show patch archiveAt 216=.mul 98 210 from rfl) ⟨by decide,by decide⟩

private theorem e217 (x : Fin 84 → Rat) : atWire x 217 = atWire x 145 * atWire x 200 := wireStep x (by decide) (show patch archiveAt 217=.mul 145 200 from rfl) ⟨by decide,by decide⟩

private theorem e218 (x : Fin 84 → Rat) : atWire x 218 = atWire x 146 * atWire x 217 := wireStep x (by decide) (show patch archiveAt 218=.mul 146 217 from rfl) ⟨by decide,by decide⟩

private theorem e219 (x : Fin 84 → Rat) : atWire x 219 = atWire x 216 + atWire x 218 := wireStep x (by decide) (show patch archiveAt 219=.add 216 218 from rfl) ⟨by decide,by decide⟩

private theorem e243 (x : Fin 84 → Rat) : atWire x 243 = (-12:Rat) := wireStep x (by decide) (show patch archiveAt 243=.int (-12) from rfl) trivial

private theorem e244 (x : Fin 84 → Rat) : atWire x 244 = (-9:Rat) := wireStep x (by decide) (show patch archiveAt 244=.int (-9) from rfl) trivial

private theorem e248 (x : Fin 84 → Rat) : atWire x 248 = (114:Rat) := wireStep x (by decide) (show patch archiveAt 248=.int (114) from rfl) trivial

private theorem e249 (x : Fin 84 → Rat) : atWire x 249 = atWire x 188 * atWire x 248 := wireStep x (by decide) (show patch archiveAt 249=.mul 188 248 from rfl) ⟨by decide,by decide⟩

private theorem e250 (x : Fin 84 → Rat) : atWire x 250 = (-14:Rat) := wireStep x (by decide) (show patch archiveAt 250=.int (-14) from rfl) trivial

private theorem e251 (x : Fin 84 → Rat) : atWire x 251 = atWire x 190 * atWire x 250 := wireStep x (by decide) (show patch archiveAt 251=.mul 190 250 from rfl) ⟨by decide,by decide⟩

private theorem e252 (x : Fin 84 → Rat) : atWire x 252 = atWire x 85 * atWire x 251 := wireStep x (by decide) (show patch archiveAt 252=.mul 85 251 from rfl) ⟨by decide,by decide⟩

private theorem e253 (x : Fin 84 → Rat) : atWire x 253 = atWire x 147 * atWire x 252 := wireStep x (by decide) (show patch archiveAt 253=.mul 147 252 from rfl) ⟨by decide,by decide⟩

private theorem e254 (x : Fin 84 → Rat) : atWire x 254 = atWire x 249 + atWire x 253 := wireStep x (by decide) (show patch archiveAt 254=.add 249 253 from rfl) ⟨by decide,by decide⟩

private theorem e255 (x : Fin 84 → Rat) : atWire x 255 = (176:Rat) := wireStep x (by decide) (show patch archiveAt 255=.int (176) from rfl) trivial

private theorem e256 (x : Fin 84 → Rat) : atWire x 256 = atWire x 254 + atWire x 255 := wireStep x (by decide) (show patch archiveAt 256=.add 254 255 from rfl) ⟨by decide,by decide⟩

private theorem e257 (x : Fin 84 → Rat) : atWire x 257 = atWire x 88 * atWire x 219 := wireStep x (by decide) (show patch archiveAt 257=.mul 88 219 from rfl) ⟨by decide,by decide⟩

private theorem e258 (x : Fin 84 → Rat) : atWire x 258 = atWire x 85 * atWire x 257 := wireStep x (by decide) (show patch archiveAt 258=.mul 85 257 from rfl) ⟨by decide,by decide⟩

private theorem e259 (x : Fin 84 → Rat) : atWire x 259 = atWire x 98 * atWire x 215 := wireStep x (by decide) (show patch archiveAt 259=.mul 98 215 from rfl) ⟨by decide,by decide⟩

private theorem e260 (x : Fin 84 → Rat) : atWire x 260 = atWire x 147 * atWire x 259 := wireStep x (by decide) (show patch archiveAt 260=.mul 147 259 from rfl) ⟨by decide,by decide⟩

private theorem e261 (x : Fin 84 → Rat) : atWire x 261 = atWire x 258 + atWire x 260 := wireStep x (by decide) (show patch archiveAt 261=.add 258 260 from rfl) ⟨by decide,by decide⟩

private theorem e262 (x : Fin 84 → Rat) : atWire x 262 = (39:Rat) := wireStep x (by decide) (show patch archiveAt 262=.int (39) from rfl) trivial

private theorem e263 (x : Fin 84 → Rat) : atWire x 263 = atWire x 183 * atWire x 262 := wireStep x (by decide) (show patch archiveAt 263=.mul 183 262 from rfl) ⟨by decide,by decide⟩

private theorem e264 (x : Fin 84 → Rat) : atWire x 264 = atWire x 185 * atWire x 244 := wireStep x (by decide) (show patch archiveAt 264=.mul 185 244 from rfl) ⟨by decide,by decide⟩

private theorem e265 (x : Fin 84 → Rat) : atWire x 265 = atWire x 85 * atWire x 264 := wireStep x (by decide) (show patch archiveAt 265=.mul 85 264 from rfl) ⟨by decide,by decide⟩

private theorem e266 (x : Fin 84 → Rat) : atWire x 266 = atWire x 147 * atWire x 265 := wireStep x (by decide) (show patch archiveAt 266=.mul 147 265 from rfl) ⟨by decide,by decide⟩

private theorem e267 (x : Fin 84 → Rat) : atWire x 267 = atWire x 263 + atWire x 266 := wireStep x (by decide) (show patch archiveAt 267=.add 263 266 from rfl) ⟨by decide,by decide⟩

private theorem e268 (x : Fin 84 → Rat) : atWire x 268 = atWire x 98 * atWire x 267 := wireStep x (by decide) (show patch archiveAt 268=.mul 98 267 from rfl) ⟨by decide,by decide⟩

private theorem e269 (x : Fin 84 → Rat) : atWire x 269 = atWire x 96 * atWire x 268 := wireStep x (by decide) (show patch archiveAt 269=.mul 96 268 from rfl) ⟨by decide,by decide⟩

private theorem e270 (x : Fin 84 → Rat) : atWire x 270 = atWire x 261 + atWire x 269 := wireStep x (by decide) (show patch archiveAt 270=.add 261 269 from rfl) ⟨by decide,by decide⟩

private theorem e272 (x : Fin 84 → Rat) : atWire x 272 = atWire x 88 * atWire x 215 := wireStep x (by decide) (show patch archiveAt 272=.mul 88 215 from rfl) ⟨by decide,by decide⟩

private theorem e273 (x : Fin 84 → Rat) : atWire x 273 = atWire x 98 * atWire x 219 := wireStep x (by decide) (show patch archiveAt 273=.mul 98 219 from rfl) ⟨by decide,by decide⟩

private theorem e274 (x : Fin 84 → Rat) : atWire x 274 = atWire x 147 * atWire x 273 := wireStep x (by decide) (show patch archiveAt 274=.mul 147 273 from rfl) ⟨by decide,by decide⟩

private theorem e275 (x : Fin 84 → Rat) : atWire x 275 = atWire x 272 + atWire x 274 := wireStep x (by decide) (show patch archiveAt 275=.add 272 274 from rfl) ⟨by decide,by decide⟩

private theorem e276 (x : Fin 84 → Rat) : atWire x 276 = atWire x 185 * atWire x 262 := wireStep x (by decide) (show patch archiveAt 276=.mul 185 262 from rfl) ⟨by decide,by decide⟩

private theorem e277 (x : Fin 84 → Rat) : atWire x 277 = atWire x 183 * atWire x 244 := wireStep x (by decide) (show patch archiveAt 277=.mul 183 244 from rfl) ⟨by decide,by decide⟩

private theorem e278 (x : Fin 84 → Rat) : atWire x 278 = atWire x 147 * atWire x 277 := wireStep x (by decide) (show patch archiveAt 278=.mul 147 277 from rfl) ⟨by decide,by decide⟩

private theorem e279 (x : Fin 84 → Rat) : atWire x 279 = atWire x 276 + atWire x 278 := wireStep x (by decide) (show patch archiveAt 279=.add 276 278 from rfl) ⟨by decide,by decide⟩

private theorem e280 (x : Fin 84 → Rat) : atWire x 280 = atWire x 98 * atWire x 279 := wireStep x (by decide) (show patch archiveAt 280=.mul 98 279 from rfl) ⟨by decide,by decide⟩

private theorem e281 (x : Fin 84 → Rat) : atWire x 281 = atWire x 96 * atWire x 280 := wireStep x (by decide) (show patch archiveAt 281=.mul 96 280 from rfl) ⟨by decide,by decide⟩

private theorem e282 (x : Fin 84 → Rat) : atWire x 282 = atWire x 275 + atWire x 281 := wireStep x (by decide) (show patch archiveAt 282=.add 275 281 from rfl) ⟨by decide,by decide⟩

private theorem e283 (x : Fin 84 → Rat) : atWire x 283 = atWire x 190 * atWire x 248 := wireStep x (by decide) (show patch archiveAt 283=.mul 190 248 from rfl) ⟨by decide,by decide⟩

private theorem e284 (x : Fin 84 → Rat) : atWire x 284 = atWire x 188 * atWire x 250 := wireStep x (by decide) (show patch archiveAt 284=.mul 188 250 from rfl) ⟨by decide,by decide⟩

private theorem e285 (x : Fin 84 → Rat) : atWire x 285 = atWire x 147 * atWire x 284 := wireStep x (by decide) (show patch archiveAt 285=.mul 147 284 from rfl) ⟨by decide,by decide⟩

private theorem e286 (x : Fin 84 → Rat) : atWire x 286 = atWire x 283 + atWire x 285 := wireStep x (by decide) (show patch archiveAt 286=.add 283 285 from rfl) ⟨by decide,by decide⟩

private theorem e287 (x : Fin 84 → Rat) : atWire x 287 = (-96:Rat) := wireStep x (by decide) (show patch archiveAt 287=.int (-96) from rfl) trivial

private theorem e288 (x : Fin 84 → Rat) : atWire x 288 = atWire x 286 + atWire x 287 := wireStep x (by decide) (show patch archiveAt 288=.add 286 287 from rfl) ⟨by decide,by decide⟩

private theorem e289 (x : Fin 84 → Rat) : atWire x 289 = atWire x 98 * atWire x 288 := wireStep x (by decide) (show patch archiveAt 289=.mul 98 288 from rfl) ⟨by decide,by decide⟩

private theorem e293 (x : Fin 84 → Rat) : atWire x 293 = (256:Rat) := wireStep x (by decide) (show patch archiveAt 293=.int (256) from rfl) trivial

private theorem e295 (x : Fin 84 → Rat) : atWire x 295 = J := by
  have raw : atWire x 295 = (19864055385593239154874661487684505155399757968004009706812421498807535944992309105738482240674768974773705847580926652264689771639736367352775840921871390970737855817143941343079621867684259664086415220729212607871462646467232721744593857794251711160664874078519907169726363339569967249961733805726622185910321207638883960123735373905133540510469868843854263152177920967715467145730529947004592798372140460965782072987227:Rat) :=
    wireStep x (by decide) (show patch archiveAt 295=.int (19864055385593239154874661487684505155399757968004009706812421498807535944992309105738482240674768974773705847580926652264689771639736367352775840921871390970737855817143941343079621867684259664086415220729212607871462646467232721744593857794251711160664874078519907169726363339569967249961733805726622185910321207638883960123735373905133540510469868843854263152177920967715467145730529947004592798372140460965782072987227) from rfl) trivial
  rw [raw,J]
  decide +kernel

private theorem e296 (x : Fin 84 → Rat) : atWire x 296 = atWire x 256 * atWire x 256 := wireStep x (by decide) (show patch archiveAt 296=.mul 256 256 from rfl) ⟨by decide,by decide⟩

private theorem e297 (x : Fin 84 → Rat) : atWire x 297 = atWire x 288 * atWire x 288 := wireStep x (by decide) (show patch archiveAt 297=.mul 288 288 from rfl) ⟨by decide,by decide⟩

private theorem e298 (x : Fin 84 → Rat) : atWire x 298 = atWire x 148 * atWire x 297 := wireStep x (by decide) (show patch archiveAt 298=.mul 148 297 from rfl) ⟨by decide,by decide⟩

private theorem e299 (x : Fin 84 → Rat) : atWire x 299 = atWire x 296 + atWire x 298 := wireStep x (by decide) (show patch archiveAt 299=.add 296 298 from rfl) ⟨by decide,by decide⟩

private theorem e300 (x : Fin 84 → Rat) : atWire x 300 = atWire x 295 * atWire x 299 := wireStep x (by decide) (show patch archiveAt 300=.mul 295 299 from rfl) ⟨by decide,by decide⟩

private theorem e301 (x : Fin 84 → Rat) : atWire x 301 = (307328:Rat) := wireStep x (by decide) (show patch archiveAt 301=.int (307328) from rfl) trivial

private theorem e302 (x : Fin 84 → Rat) : atWire x 302 = atWire x 270 * atWire x 289 := wireStep x (by decide) (show patch archiveAt 302=.mul 270 289 from rfl) ⟨by decide,by decide⟩

private theorem e303 (x : Fin 84 → Rat) : atWire x 303 = atWire x 256 * atWire x 282 := wireStep x (by decide) (show patch archiveAt 303=.mul 256 282 from rfl) ⟨by decide,by decide⟩

private theorem e304 (x : Fin 84 → Rat) : atWire x 304 = atWire x 302 + atWire x 303 := wireStep x (by decide) (show patch archiveAt 304=.add 302 303 from rfl) ⟨by decide,by decide⟩

private theorem e305 (x : Fin 84 → Rat) : atWire x 305 = atWire x 293 * atWire x 304 := wireStep x (by decide) (show patch archiveAt 305=.mul 293 304 from rfl) ⟨by decide,by decide⟩

private theorem e306 (x : Fin 84 → Rat) : atWire x 306 = atWire x 300 * atWire x 300 := wireStep x (by decide) (show patch archiveAt 306=.mul 300 300 from rfl) ⟨by decide,by decide⟩

private theorem e307 (x : Fin 84 → Rat) : atWire x 307 = (94450499584:Rat) := wireStep x (by decide) (show patch archiveAt 307=.int (94450499584) from rfl) trivial

private theorem e308 (x : Fin 84 → Rat) : atWire x 308 = 1*(atWire x 182)^2 := by
  have raw : atWire x 308 = (25705455471670699433133086310504970403715321030168424633699464997547202967294600382340356864840920242534609860043703580766898611376020646207324507842758072816714600293371782640955963124826622986068174849236342614311579299762272094845817375769121376914784382735886412671731445651447369:Rat) :=
    wireStep x (by decide) (show patch archiveAt 308=.int (25705455471670699433133086310504970403715321030168424633699464997547202967294600382340356864840920242534609860043703580766898611376020646207324507842758072816714600293371782640955963124826622986068174849236342614311579299762272094845817375769121376914784382735886412671731445651447369) from rfl) trivial
  rw [raw,HeightSpecialization.root_scale]
  decide +kernel

private theorem e309 (x : Fin 84 → Rat) : atWire x 309 = atWire x 1 * atWire x 308 := wireStep x (by decide) (show patch archiveAt 309=.mul 1 308 from rfl) ⟨by decide,by decide⟩

private theorem e310 (x : Fin 84 → Rat) : atWire x 310 = atWire x 1 * atWire x 309 := wireStep x (by decide) (show patch archiveAt 310=.mul 1 309 from rfl) ⟨by decide,by decide⟩

private theorem e311 (x : Fin 84 → Rat) : atWire x 311 = atWire x 4 * atWire x 310 := wireStep x (by decide) (show patch archiveAt 311=.mul 4 310 from rfl) ⟨by decide,by decide⟩

private theorem e312 (x : Fin 84 → Rat) : atWire x 312 = atWire x 4 * atWire x 311 := wireStep x (by decide) (show patch archiveAt 312=.mul 4 311 from rfl) ⟨by decide,by decide⟩

private theorem e313 (x : Fin 84 → Rat) : atWire x 313 = atWire x 6 * atWire x 312 := wireStep x (by decide) (show patch archiveAt 313=.mul 6 312 from rfl) ⟨by decide,by decide⟩

private theorem e314 (x : Fin 84 → Rat) : atWire x 314 = atWire x 6 * atWire x 313 := wireStep x (by decide) (show patch archiveAt 314=.mul 6 313 from rfl) ⟨by decide,by decide⟩

private theorem e315 (x : Fin 84 → Rat) : atWire x 315 = 2*(atWire x 182)^2 := by
  have raw : atWire x 315 = (51410910943341398866266172621009940807430642060336849267398929995094405934589200764680713729681840485069219720087407161533797222752041292414649015685516145633429200586743565281911926249653245972136349698472685228623158599524544189691634751538242753829568765471772825343462891302894738:Rat) :=
    wireStep x (by decide) (show patch archiveAt 315=.int (51410910943341398866266172621009940807430642060336849267398929995094405934589200764680713729681840485069219720087407161533797222752041292414649015685516145633429200586743565281911926249653245972136349698472685228623158599524544189691634751538242753829568765471772825343462891302894738) from rfl) trivial
  rw [raw,HeightSpecialization.root_scale]
  decide +kernel

private theorem e316 (x : Fin 84 → Rat) : atWire x 316 = atWire x 1 * atWire x 315 := wireStep x (by decide) (show patch archiveAt 316=.mul 1 315 from rfl) ⟨by decide,by decide⟩

private theorem e317 (x : Fin 84 → Rat) : atWire x 317 = atWire x 1 * atWire x 316 := wireStep x (by decide) (show patch archiveAt 317=.mul 1 316 from rfl) ⟨by decide,by decide⟩

private theorem e318 (x : Fin 84 → Rat) : atWire x 318 = atWire x 4 * atWire x 317 := wireStep x (by decide) (show patch archiveAt 318=.mul 4 317 from rfl) ⟨by decide,by decide⟩

private theorem e319 (x : Fin 84 → Rat) : atWire x 319 = atWire x 4 * atWire x 318 := wireStep x (by decide) (show patch archiveAt 319=.mul 4 318 from rfl) ⟨by decide,by decide⟩

private theorem e320 (x : Fin 84 → Rat) : atWire x 320 = atWire x 7 * atWire x 319 := wireStep x (by decide) (show patch archiveAt 320=.mul 7 319 from rfl) ⟨by decide,by decide⟩

private theorem e321 (x : Fin 84 → Rat) : atWire x 321 = atWire x 7 * atWire x 320 := wireStep x (by decide) (show patch archiveAt 321=.mul 7 320 from rfl) ⟨by decide,by decide⟩

private theorem e322 (x : Fin 84 → Rat) : atWire x 322 = atWire x 314 + atWire x 321 := wireStep x (by decide) (show patch archiveAt 322=.add 314 321 from rfl) ⟨by decide,by decide⟩

private theorem e323 (x : Fin 84 → Rat) : atWire x 323 = 8*(atWire x 182)^2 := by
  have raw : atWire x 323 = (205643643773365595465064690484039763229722568241347397069595719980377623738356803058722854918727361940276878880349628646135188891008165169658596062742064582533716802346974261127647704998612983888545398793890740914492634398098176758766539006152971015318275061887091301373851565211578952:Rat) :=
    wireStep x (by decide) (show patch archiveAt 323=.int (205643643773365595465064690484039763229722568241347397069595719980377623738356803058722854918727361940276878880349628646135188891008165169658596062742064582533716802346974261127647704998612983888545398793890740914492634398098176758766539006152971015318275061887091301373851565211578952) from rfl) trivial
  rw [raw,HeightSpecialization.root_scale]
  decide +kernel

private theorem e324 (x : Fin 84 → Rat) : atWire x 324 = atWire x 1 * atWire x 323 := wireStep x (by decide) (show patch archiveAt 324=.mul 1 323 from rfl) ⟨by decide,by decide⟩

private theorem e325 (x : Fin 84 → Rat) : atWire x 325 = atWire x 1 * atWire x 324 := wireStep x (by decide) (show patch archiveAt 325=.mul 1 324 from rfl) ⟨by decide,by decide⟩

private theorem e326 (x : Fin 84 → Rat) : atWire x 326 = atWire x 4 * atWire x 325 := wireStep x (by decide) (show patch archiveAt 326=.mul 4 325 from rfl) ⟨by decide,by decide⟩

private theorem e327 (x : Fin 84 → Rat) : atWire x 327 = atWire x 5 * atWire x 326 := wireStep x (by decide) (show patch archiveAt 327=.mul 5 326 from rfl) ⟨by decide,by decide⟩

private theorem e328 (x : Fin 84 → Rat) : atWire x 328 = atWire x 6 * atWire x 327 := wireStep x (by decide) (show patch archiveAt 328=.mul 6 327 from rfl) ⟨by decide,by decide⟩

private theorem e329 (x : Fin 84 → Rat) : atWire x 329 = atWire x 7 * atWire x 328 := wireStep x (by decide) (show patch archiveAt 329=.mul 7 328 from rfl) ⟨by decide,by decide⟩

private theorem e330 (x : Fin 84 → Rat) : atWire x 330 = atWire x 322 + atWire x 329 := wireStep x (by decide) (show patch archiveAt 330=.add 322 329 from rfl) ⟨by decide,by decide⟩

private theorem e331 (x : Fin 84 → Rat) : atWire x 331 = atWire x 5 * atWire x 317 := wireStep x (by decide) (show patch archiveAt 331=.mul 5 317 from rfl) ⟨by decide,by decide⟩

private theorem e332 (x : Fin 84 → Rat) : atWire x 332 = atWire x 5 * atWire x 331 := wireStep x (by decide) (show patch archiveAt 332=.mul 5 331 from rfl) ⟨by decide,by decide⟩

private theorem e333 (x : Fin 84 → Rat) : atWire x 333 = atWire x 6 * atWire x 332 := wireStep x (by decide) (show patch archiveAt 333=.mul 6 332 from rfl) ⟨by decide,by decide⟩

private theorem e334 (x : Fin 84 → Rat) : atWire x 334 = atWire x 6 * atWire x 333 := wireStep x (by decide) (show patch archiveAt 334=.mul 6 333 from rfl) ⟨by decide,by decide⟩

private theorem e335 (x : Fin 84 → Rat) : atWire x 335 = atWire x 330 + atWire x 334 := wireStep x (by decide) (show patch archiveAt 335=.add 330 334 from rfl) ⟨by decide,by decide⟩

private theorem e336 (x : Fin 84 → Rat) : atWire x 336 = 4*(atWire x 182)^2 := by
  have raw : atWire x 336 = (102821821886682797732532345242019881614861284120673698534797859990188811869178401529361427459363680970138439440174814323067594445504082584829298031371032291266858401173487130563823852499306491944272699396945370457246317199049088379383269503076485507659137530943545650686925782605789476:Rat) :=
    wireStep x (by decide) (show patch archiveAt 336=.int (102821821886682797732532345242019881614861284120673698534797859990188811869178401529361427459363680970138439440174814323067594445504082584829298031371032291266858401173487130563823852499306491944272699396945370457246317199049088379383269503076485507659137530943545650686925782605789476) from rfl) trivial
  rw [raw,HeightSpecialization.root_scale]
  decide +kernel

private theorem e337 (x : Fin 84 → Rat) : atWire x 337 = atWire x 1 * atWire x 336 := wireStep x (by decide) (show patch archiveAt 337=.mul 1 336 from rfl) ⟨by decide,by decide⟩

private theorem e338 (x : Fin 84 → Rat) : atWire x 338 = atWire x 1 * atWire x 337 := wireStep x (by decide) (show patch archiveAt 338=.mul 1 337 from rfl) ⟨by decide,by decide⟩

private theorem e339 (x : Fin 84 → Rat) : atWire x 339 = atWire x 5 * atWire x 338 := wireStep x (by decide) (show patch archiveAt 339=.mul 5 338 from rfl) ⟨by decide,by decide⟩

private theorem e340 (x : Fin 84 → Rat) : atWire x 340 = atWire x 5 * atWire x 339 := wireStep x (by decide) (show patch archiveAt 340=.mul 5 339 from rfl) ⟨by decide,by decide⟩

private theorem e341 (x : Fin 84 → Rat) : atWire x 341 = atWire x 7 * atWire x 340 := wireStep x (by decide) (show patch archiveAt 341=.mul 7 340 from rfl) ⟨by decide,by decide⟩

private theorem e342 (x : Fin 84 → Rat) : atWire x 342 = atWire x 7 * atWire x 341 := wireStep x (by decide) (show patch archiveAt 342=.mul 7 341 from rfl) ⟨by decide,by decide⟩

private theorem e343 (x : Fin 84 → Rat) : atWire x 343 = atWire x 335 + atWire x 342 := wireStep x (by decide) (show patch archiveAt 343=.add 335 342 from rfl) ⟨by decide,by decide⟩

private theorem e344 (x : Fin 84 → Rat) : atWire x 344 = atWire x 2 * atWire x 324 := wireStep x (by decide) (show patch archiveAt 344=.mul 2 324 from rfl) ⟨by decide,by decide⟩

private theorem e345 (x : Fin 84 → Rat) : atWire x 345 = atWire x 4 * atWire x 344 := wireStep x (by decide) (show patch archiveAt 345=.mul 4 344 from rfl) ⟨by decide,by decide⟩

private theorem e346 (x : Fin 84 → Rat) : atWire x 346 = atWire x 4 * atWire x 345 := wireStep x (by decide) (show patch archiveAt 346=.mul 4 345 from rfl) ⟨by decide,by decide⟩

private theorem e347 (x : Fin 84 → Rat) : atWire x 347 = atWire x 6 * atWire x 346 := wireStep x (by decide) (show patch archiveAt 347=.mul 6 346 from rfl) ⟨by decide,by decide⟩

private theorem e348 (x : Fin 84 → Rat) : atWire x 348 = atWire x 7 * atWire x 347 := wireStep x (by decide) (show patch archiveAt 348=.mul 7 347 from rfl) ⟨by decide,by decide⟩

private theorem e349 (x : Fin 84 → Rat) : atWire x 349 = atWire x 343 + atWire x 348 := wireStep x (by decide) (show patch archiveAt 349=.add 343 348 from rfl) ⟨by decide,by decide⟩

private theorem e350 (x : Fin 84 → Rat) : atWire x 350 = atWire x 5 * atWire x 345 := wireStep x (by decide) (show patch archiveAt 350=.mul 5 345 from rfl) ⟨by decide,by decide⟩

private theorem e351 (x : Fin 84 → Rat) : atWire x 351 = atWire x 6 * atWire x 350 := wireStep x (by decide) (show patch archiveAt 351=.mul 6 350 from rfl) ⟨by decide,by decide⟩

private theorem e352 (x : Fin 84 → Rat) : atWire x 352 = atWire x 6 * atWire x 351 := wireStep x (by decide) (show patch archiveAt 352=.mul 6 351 from rfl) ⟨by decide,by decide⟩

private theorem e353 (x : Fin 84 → Rat) : atWire x 353 = atWire x 349 + atWire x 352 := wireStep x (by decide) (show patch archiveAt 353=.add 349 352 from rfl) ⟨by decide,by decide⟩

private theorem e354 (x : Fin 84 → Rat) : atWire x 354 = 16*(atWire x 182)^2 := by
  have raw : atWire x 354 = (411287287546731190930129380968079526459445136482694794139191439960755247476713606117445709837454723880553757760699257292270377782016330339317192125484129165067433604693948522255295409997225967777090797587781481828985268796196353517533078012305942030636550123774182602747703130423157904:Rat) :=
    wireStep x (by decide) (show patch archiveAt 354=.int (411287287546731190930129380968079526459445136482694794139191439960755247476713606117445709837454723880553757760699257292270377782016330339317192125484129165067433604693948522255295409997225967777090797587781481828985268796196353517533078012305942030636550123774182602747703130423157904) from rfl) trivial
  rw [raw,HeightSpecialization.root_scale]
  decide +kernel

private theorem e355 (x : Fin 84 → Rat) : atWire x 355 = atWire x 1 * atWire x 354 := wireStep x (by decide) (show patch archiveAt 355=.mul 1 354 from rfl) ⟨by decide,by decide⟩

private theorem e356 (x : Fin 84 → Rat) : atWire x 356 = atWire x 2 * atWire x 355 := wireStep x (by decide) (show patch archiveAt 356=.mul 2 355 from rfl) ⟨by decide,by decide⟩

private theorem e357 (x : Fin 84 → Rat) : atWire x 357 = atWire x 4 * atWire x 356 := wireStep x (by decide) (show patch archiveAt 357=.mul 4 356 from rfl) ⟨by decide,by decide⟩

private theorem e358 (x : Fin 84 → Rat) : atWire x 358 = atWire x 5 * atWire x 357 := wireStep x (by decide) (show patch archiveAt 358=.mul 5 357 from rfl) ⟨by decide,by decide⟩

private theorem e359 (x : Fin 84 → Rat) : atWire x 359 = atWire x 7 * atWire x 358 := wireStep x (by decide) (show patch archiveAt 359=.mul 7 358 from rfl) ⟨by decide,by decide⟩

private theorem e360 (x : Fin 84 → Rat) : atWire x 360 = atWire x 7 * atWire x 359 := wireStep x (by decide) (show patch archiveAt 360=.mul 7 359 from rfl) ⟨by decide,by decide⟩

private theorem e361 (x : Fin 84 → Rat) : atWire x 361 = atWire x 353 + atWire x 360 := wireStep x (by decide) (show patch archiveAt 361=.add 353 360 from rfl) ⟨by decide,by decide⟩

private theorem e362 (x : Fin 84 → Rat) : atWire x 362 = atWire x 5 * atWire x 356 := wireStep x (by decide) (show patch archiveAt 362=.mul 5 356 from rfl) ⟨by decide,by decide⟩

private theorem e363 (x : Fin 84 → Rat) : atWire x 363 = atWire x 5 * atWire x 362 := wireStep x (by decide) (show patch archiveAt 363=.mul 5 362 from rfl) ⟨by decide,by decide⟩

private theorem e364 (x : Fin 84 → Rat) : atWire x 364 = atWire x 6 * atWire x 363 := wireStep x (by decide) (show patch archiveAt 364=.mul 6 363 from rfl) ⟨by decide,by decide⟩

private theorem e365 (x : Fin 84 → Rat) : atWire x 365 = atWire x 7 * atWire x 364 := wireStep x (by decide) (show patch archiveAt 365=.mul 7 364 from rfl) ⟨by decide,by decide⟩

private theorem e366 (x : Fin 84 → Rat) : atWire x 366 = atWire x 361 + atWire x 365 := wireStep x (by decide) (show patch archiveAt 366=.add 361 365 from rfl) ⟨by decide,by decide⟩

private theorem e367 (x : Fin 84 → Rat) : atWire x 367 = atWire x 2 * atWire x 315 := wireStep x (by decide) (show patch archiveAt 367=.mul 2 315 from rfl) ⟨by decide,by decide⟩

private theorem e368 (x : Fin 84 → Rat) : atWire x 368 = atWire x 2 * atWire x 367 := wireStep x (by decide) (show patch archiveAt 368=.mul 2 367 from rfl) ⟨by decide,by decide⟩

private theorem e369 (x : Fin 84 → Rat) : atWire x 369 = atWire x 4 * atWire x 368 := wireStep x (by decide) (show patch archiveAt 369=.mul 4 368 from rfl) ⟨by decide,by decide⟩

private theorem e370 (x : Fin 84 → Rat) : atWire x 370 = atWire x 4 * atWire x 369 := wireStep x (by decide) (show patch archiveAt 370=.mul 4 369 from rfl) ⟨by decide,by decide⟩

private theorem e371 (x : Fin 84 → Rat) : atWire x 371 = atWire x 6 * atWire x 370 := wireStep x (by decide) (show patch archiveAt 371=.mul 6 370 from rfl) ⟨by decide,by decide⟩

private theorem e372 (x : Fin 84 → Rat) : atWire x 372 = atWire x 6 * atWire x 371 := wireStep x (by decide) (show patch archiveAt 372=.mul 6 371 from rfl) ⟨by decide,by decide⟩

private theorem e373 (x : Fin 84 → Rat) : atWire x 373 = atWire x 366 + atWire x 372 := wireStep x (by decide) (show patch archiveAt 373=.add 366 372 from rfl) ⟨by decide,by decide⟩

private theorem e374 (x : Fin 84 → Rat) : atWire x 374 = atWire x 2 * atWire x 336 := wireStep x (by decide) (show patch archiveAt 374=.mul 2 336 from rfl) ⟨by decide,by decide⟩

private theorem e375 (x : Fin 84 → Rat) : atWire x 375 = atWire x 2 * atWire x 374 := wireStep x (by decide) (show patch archiveAt 375=.mul 2 374 from rfl) ⟨by decide,by decide⟩

private theorem e376 (x : Fin 84 → Rat) : atWire x 376 = atWire x 4 * atWire x 375 := wireStep x (by decide) (show patch archiveAt 376=.mul 4 375 from rfl) ⟨by decide,by decide⟩

private theorem e377 (x : Fin 84 → Rat) : atWire x 377 = atWire x 4 * atWire x 376 := wireStep x (by decide) (show patch archiveAt 377=.mul 4 376 from rfl) ⟨by decide,by decide⟩

private theorem e378 (x : Fin 84 → Rat) : atWire x 378 = atWire x 7 * atWire x 377 := wireStep x (by decide) (show patch archiveAt 378=.mul 7 377 from rfl) ⟨by decide,by decide⟩

private theorem e379 (x : Fin 84 → Rat) : atWire x 379 = atWire x 7 * atWire x 378 := wireStep x (by decide) (show patch archiveAt 379=.mul 7 378 from rfl) ⟨by decide,by decide⟩

private theorem e380 (x : Fin 84 → Rat) : atWire x 380 = atWire x 373 + atWire x 379 := wireStep x (by decide) (show patch archiveAt 380=.add 373 379 from rfl) ⟨by decide,by decide⟩

private theorem e381 (x : Fin 84 → Rat) : atWire x 381 = atWire x 2 * atWire x 354 := wireStep x (by decide) (show patch archiveAt 381=.mul 2 354 from rfl) ⟨by decide,by decide⟩

private theorem e382 (x : Fin 84 → Rat) : atWire x 382 = atWire x 2 * atWire x 381 := wireStep x (by decide) (show patch archiveAt 382=.mul 2 381 from rfl) ⟨by decide,by decide⟩

private theorem e383 (x : Fin 84 → Rat) : atWire x 383 = atWire x 4 * atWire x 382 := wireStep x (by decide) (show patch archiveAt 383=.mul 4 382 from rfl) ⟨by decide,by decide⟩

private theorem e384 (x : Fin 84 → Rat) : atWire x 384 = atWire x 5 * atWire x 383 := wireStep x (by decide) (show patch archiveAt 384=.mul 5 383 from rfl) ⟨by decide,by decide⟩

private theorem e385 (x : Fin 84 → Rat) : atWire x 385 = atWire x 6 * atWire x 384 := wireStep x (by decide) (show patch archiveAt 385=.mul 6 384 from rfl) ⟨by decide,by decide⟩

private theorem e386 (x : Fin 84 → Rat) : atWire x 386 = atWire x 7 * atWire x 385 := wireStep x (by decide) (show patch archiveAt 386=.mul 7 385 from rfl) ⟨by decide,by decide⟩

private theorem e387 (x : Fin 84 → Rat) : atWire x 387 = atWire x 380 + atWire x 386 := wireStep x (by decide) (show patch archiveAt 387=.add 380 386 from rfl) ⟨by decide,by decide⟩

private theorem e388 (x : Fin 84 → Rat) : atWire x 388 = atWire x 5 * atWire x 375 := wireStep x (by decide) (show patch archiveAt 388=.mul 5 375 from rfl) ⟨by decide,by decide⟩

private theorem e389 (x : Fin 84 → Rat) : atWire x 389 = atWire x 5 * atWire x 388 := wireStep x (by decide) (show patch archiveAt 389=.mul 5 388 from rfl) ⟨by decide,by decide⟩

private theorem e390 (x : Fin 84 → Rat) : atWire x 390 = atWire x 6 * atWire x 389 := wireStep x (by decide) (show patch archiveAt 390=.mul 6 389 from rfl) ⟨by decide,by decide⟩

private theorem e391 (x : Fin 84 → Rat) : atWire x 391 = atWire x 6 * atWire x 390 := wireStep x (by decide) (show patch archiveAt 391=.mul 6 390 from rfl) ⟨by decide,by decide⟩

private theorem e392 (x : Fin 84 → Rat) : atWire x 392 = atWire x 387 + atWire x 391 := wireStep x (by decide) (show patch archiveAt 392=.add 387 391 from rfl) ⟨by decide,by decide⟩

private theorem e393 (x : Fin 84 → Rat) : atWire x 393 = atWire x 2 * atWire x 323 := wireStep x (by decide) (show patch archiveAt 393=.mul 2 323 from rfl) ⟨by decide,by decide⟩

private theorem e394 (x : Fin 84 → Rat) : atWire x 394 = atWire x 2 * atWire x 393 := wireStep x (by decide) (show patch archiveAt 394=.mul 2 393 from rfl) ⟨by decide,by decide⟩

private theorem e395 (x : Fin 84 → Rat) : atWire x 395 = atWire x 5 * atWire x 394 := wireStep x (by decide) (show patch archiveAt 395=.mul 5 394 from rfl) ⟨by decide,by decide⟩

private theorem e396 (x : Fin 84 → Rat) : atWire x 396 = atWire x 5 * atWire x 395 := wireStep x (by decide) (show patch archiveAt 396=.mul 5 395 from rfl) ⟨by decide,by decide⟩

private theorem e397 (x : Fin 84 → Rat) : atWire x 397 = atWire x 7 * atWire x 396 := wireStep x (by decide) (show patch archiveAt 397=.mul 7 396 from rfl) ⟨by decide,by decide⟩

private theorem e398 (x : Fin 84 → Rat) : atWire x 398 = atWire x 7 * atWire x 397 := wireStep x (by decide) (show patch archiveAt 398=.mul 7 397 from rfl) ⟨by decide,by decide⟩

private theorem e399 (x : Fin 84 → Rat) : atWire x 399 = atWire x 392 + atWire x 398 := wireStep x (by decide) (show patch archiveAt 399=.add 392 398 from rfl) ⟨by decide,by decide⟩

private theorem e400 (x : Fin 84 → Rat) : atWire x 400 = atWire x 7 * atWire x 313 := wireStep x (by decide) (show patch archiveAt 400=.mul 7 313 from rfl) ⟨by decide,by decide⟩

private theorem e401 (x : Fin 84 → Rat) : atWire x 401 = atWire x 5 * atWire x 311 := wireStep x (by decide) (show patch archiveAt 401=.mul 5 311 from rfl) ⟨by decide,by decide⟩

private theorem e402 (x : Fin 84 → Rat) : atWire x 402 = atWire x 6 * atWire x 401 := wireStep x (by decide) (show patch archiveAt 402=.mul 6 401 from rfl) ⟨by decide,by decide⟩

private theorem e403 (x : Fin 84 → Rat) : atWire x 403 = atWire x 6 * atWire x 402 := wireStep x (by decide) (show patch archiveAt 403=.mul 6 402 from rfl) ⟨by decide,by decide⟩

private theorem e404 (x : Fin 84 → Rat) : atWire x 404 = atWire x 400 + atWire x 403 := wireStep x (by decide) (show patch archiveAt 404=.add 400 403 from rfl) ⟨by decide,by decide⟩

private theorem e405 (x : Fin 84 → Rat) : atWire x 405 = atWire x 5 * atWire x 318 := wireStep x (by decide) (show patch archiveAt 405=.mul 5 318 from rfl) ⟨by decide,by decide⟩

private theorem e406 (x : Fin 84 → Rat) : atWire x 406 = atWire x 7 * atWire x 405 := wireStep x (by decide) (show patch archiveAt 406=.mul 7 405 from rfl) ⟨by decide,by decide⟩

private theorem e407 (x : Fin 84 → Rat) : atWire x 407 = atWire x 7 * atWire x 406 := wireStep x (by decide) (show patch archiveAt 407=.mul 7 406 from rfl) ⟨by decide,by decide⟩

private theorem e408 (x : Fin 84 → Rat) : atWire x 408 = atWire x 404 + atWire x 407 := wireStep x (by decide) (show patch archiveAt 408=.add 404 407 from rfl) ⟨by decide,by decide⟩

private theorem e409 (x : Fin 84 → Rat) : atWire x 409 = atWire x 7 * atWire x 333 := wireStep x (by decide) (show patch archiveAt 409=.mul 7 333 from rfl) ⟨by decide,by decide⟩

private theorem e410 (x : Fin 84 → Rat) : atWire x 410 = atWire x 408 + atWire x 409 := wireStep x (by decide) (show patch archiveAt 410=.add 408 409 from rfl) ⟨by decide,by decide⟩

private theorem e411 (x : Fin 84 → Rat) : atWire x 411 = atWire x 2 * atWire x 309 := wireStep x (by decide) (show patch archiveAt 411=.mul 2 309 from rfl) ⟨by decide,by decide⟩

private theorem e412 (x : Fin 84 → Rat) : atWire x 412 = atWire x 4 * atWire x 411 := wireStep x (by decide) (show patch archiveAt 412=.mul 4 411 from rfl) ⟨by decide,by decide⟩

private theorem e413 (x : Fin 84 → Rat) : atWire x 413 = atWire x 4 * atWire x 412 := wireStep x (by decide) (show patch archiveAt 413=.mul 4 412 from rfl) ⟨by decide,by decide⟩

private theorem e414 (x : Fin 84 → Rat) : atWire x 414 = atWire x 6 * atWire x 413 := wireStep x (by decide) (show patch archiveAt 414=.mul 6 413 from rfl) ⟨by decide,by decide⟩

private theorem e415 (x : Fin 84 → Rat) : atWire x 415 = atWire x 6 * atWire x 414 := wireStep x (by decide) (show patch archiveAt 415=.mul 6 414 from rfl) ⟨by decide,by decide⟩

private theorem e416 (x : Fin 84 → Rat) : atWire x 416 = atWire x 410 + atWire x 415 := wireStep x (by decide) (show patch archiveAt 416=.add 410 415 from rfl) ⟨by decide,by decide⟩

private theorem e417 (x : Fin 84 → Rat) : atWire x 417 = atWire x 2 * atWire x 316 := wireStep x (by decide) (show patch archiveAt 417=.mul 2 316 from rfl) ⟨by decide,by decide⟩

private theorem e418 (x : Fin 84 → Rat) : atWire x 418 = atWire x 4 * atWire x 417 := wireStep x (by decide) (show patch archiveAt 418=.mul 4 417 from rfl) ⟨by decide,by decide⟩

private theorem e419 (x : Fin 84 → Rat) : atWire x 419 = atWire x 4 * atWire x 418 := wireStep x (by decide) (show patch archiveAt 419=.mul 4 418 from rfl) ⟨by decide,by decide⟩

private theorem e420 (x : Fin 84 → Rat) : atWire x 420 = atWire x 7 * atWire x 419 := wireStep x (by decide) (show patch archiveAt 420=.mul 7 419 from rfl) ⟨by decide,by decide⟩

private theorem e421 (x : Fin 84 → Rat) : atWire x 421 = atWire x 7 * atWire x 420 := wireStep x (by decide) (show patch archiveAt 421=.mul 7 420 from rfl) ⟨by decide,by decide⟩

private theorem e422 (x : Fin 84 → Rat) : atWire x 422 = atWire x 416 + atWire x 421 := wireStep x (by decide) (show patch archiveAt 422=.add 416 421 from rfl) ⟨by decide,by decide⟩

private theorem e423 (x : Fin 84 → Rat) : atWire x 423 = atWire x 7 * atWire x 351 := wireStep x (by decide) (show patch archiveAt 423=.mul 7 351 from rfl) ⟨by decide,by decide⟩

private theorem e424 (x : Fin 84 → Rat) : atWire x 424 = atWire x 422 + atWire x 423 := wireStep x (by decide) (show patch archiveAt 424=.add 422 423 from rfl) ⟨by decide,by decide⟩

private theorem e425 (x : Fin 84 → Rat) : atWire x 425 = atWire x 5 * atWire x 417 := wireStep x (by decide) (show patch archiveAt 425=.mul 5 417 from rfl) ⟨by decide,by decide⟩

private theorem e426 (x : Fin 84 → Rat) : atWire x 426 = atWire x 5 * atWire x 425 := wireStep x (by decide) (show patch archiveAt 426=.mul 5 425 from rfl) ⟨by decide,by decide⟩

private theorem e427 (x : Fin 84 → Rat) : atWire x 427 = atWire x 6 * atWire x 426 := wireStep x (by decide) (show patch archiveAt 427=.mul 6 426 from rfl) ⟨by decide,by decide⟩

private theorem e428 (x : Fin 84 → Rat) : atWire x 428 = atWire x 6 * atWire x 427 := wireStep x (by decide) (show patch archiveAt 428=.mul 6 427 from rfl) ⟨by decide,by decide⟩

private theorem e429 (x : Fin 84 → Rat) : atWire x 429 = atWire x 424 + atWire x 428 := wireStep x (by decide) (show patch archiveAt 429=.add 424 428 from rfl) ⟨by decide,by decide⟩

private theorem e430 (x : Fin 84 → Rat) : atWire x 430 = atWire x 2 * atWire x 337 := wireStep x (by decide) (show patch archiveAt 430=.mul 2 337 from rfl) ⟨by decide,by decide⟩

private theorem e431 (x : Fin 84 → Rat) : atWire x 431 = atWire x 5 * atWire x 430 := wireStep x (by decide) (show patch archiveAt 431=.mul 5 430 from rfl) ⟨by decide,by decide⟩

private theorem e432 (x : Fin 84 → Rat) : atWire x 432 = atWire x 5 * atWire x 431 := wireStep x (by decide) (show patch archiveAt 432=.mul 5 431 from rfl) ⟨by decide,by decide⟩

private theorem e433 (x : Fin 84 → Rat) : atWire x 433 = atWire x 7 * atWire x 432 := wireStep x (by decide) (show patch archiveAt 433=.mul 7 432 from rfl) ⟨by decide,by decide⟩

private theorem e434 (x : Fin 84 → Rat) : atWire x 434 = atWire x 7 * atWire x 433 := wireStep x (by decide) (show patch archiveAt 434=.mul 7 433 from rfl) ⟨by decide,by decide⟩

private theorem e435 (x : Fin 84 → Rat) : atWire x 435 = atWire x 429 + atWire x 434 := wireStep x (by decide) (show patch archiveAt 435=.add 429 434 from rfl) ⟨by decide,by decide⟩

private theorem e436 (x : Fin 84 → Rat) : atWire x 436 = atWire x 7 * atWire x 371 := wireStep x (by decide) (show patch archiveAt 436=.mul 7 371 from rfl) ⟨by decide,by decide⟩

private theorem e437 (x : Fin 84 → Rat) : atWire x 437 = atWire x 435 + atWire x 436 := wireStep x (by decide) (show patch archiveAt 437=.add 435 436 from rfl) ⟨by decide,by decide⟩

private theorem e438 (x : Fin 84 → Rat) : atWire x 438 = atWire x 5 * atWire x 369 := wireStep x (by decide) (show patch archiveAt 438=.mul 5 369 from rfl) ⟨by decide,by decide⟩

private theorem e439 (x : Fin 84 → Rat) : atWire x 439 = atWire x 6 * atWire x 438 := wireStep x (by decide) (show patch archiveAt 439=.mul 6 438 from rfl) ⟨by decide,by decide⟩

private theorem e440 (x : Fin 84 → Rat) : atWire x 440 = atWire x 6 * atWire x 439 := wireStep x (by decide) (show patch archiveAt 440=.mul 6 439 from rfl) ⟨by decide,by decide⟩

private theorem e441 (x : Fin 84 → Rat) : atWire x 441 = atWire x 437 + atWire x 440 := wireStep x (by decide) (show patch archiveAt 441=.add 437 440 from rfl) ⟨by decide,by decide⟩

private theorem e442 (x : Fin 84 → Rat) : atWire x 442 = atWire x 5 * atWire x 376 := wireStep x (by decide) (show patch archiveAt 442=.mul 5 376 from rfl) ⟨by decide,by decide⟩

private theorem e443 (x : Fin 84 → Rat) : atWire x 443 = atWire x 7 * atWire x 442 := wireStep x (by decide) (show patch archiveAt 443=.mul 7 442 from rfl) ⟨by decide,by decide⟩

private theorem e444 (x : Fin 84 → Rat) : atWire x 444 = atWire x 7 * atWire x 443 := wireStep x (by decide) (show patch archiveAt 444=.mul 7 443 from rfl) ⟨by decide,by decide⟩

private theorem e445 (x : Fin 84 → Rat) : atWire x 445 = atWire x 441 + atWire x 444 := wireStep x (by decide) (show patch archiveAt 445=.add 441 444 from rfl) ⟨by decide,by decide⟩

private theorem e446 (x : Fin 84 → Rat) : atWire x 446 = atWire x 7 * atWire x 390 := wireStep x (by decide) (show patch archiveAt 446=.mul 7 390 from rfl) ⟨by decide,by decide⟩

private theorem e447 (x : Fin 84 → Rat) : atWire x 447 = atWire x 445 + atWire x 446 := wireStep x (by decide) (show patch archiveAt 447=.add 445 446 from rfl) ⟨by decide,by decide⟩

private theorem e884 (x : Fin 84 → Rat) : atWire x 884 = atWire x 243 * atWire x 305 := wireStep x (by decide) (show patch archiveAt 884=.mul 243 305 from rfl) ⟨by decide,by decide⟩

private theorem e885 (x : Fin 84 → Rat) : atWire x 885 = atWire x 305 * atWire x 884 := wireStep x (by decide) (show patch archiveAt 885=.mul 305 884 from rfl) ⟨by decide,by decide⟩

private theorem e886 (x : Fin 84 → Rat) : atWire x 886 = (-16) * H^1 := by
  have raw : atWire x 886 = (-45698587505192354547792153440897725162160570720299421571021271106750583052968178457493967759717191542283750862299917476918930864668481148813021347276014351674159289410438724695032823333025107530787866398642386869887252088466261501948119779145104670070727791530464733638633681158128656:Rat) :=
    wireStep x (by decide) (show patch archiveAt 886=.int (-45698587505192354547792153440897725162160570720299421571021271106750583052968178457493967759717191542283750862299917476918930864668481148813021347276014351674159289410438724695032823333025107530787866398642386869887252088466261501948119779145104670070727791530464733638633681158128656) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e887 (x : Fin 84 → Rat) : atWire x 887 = atWire x 15 * atWire x 886 := wireStep x (by decide) (show patch archiveAt 887=.mul 15 886 from rfl) ⟨by decide,by decide⟩

private theorem e888 (x : Fin 84 → Rat) : atWire x 888 = (324:Rat) := wireStep x (by decide) (show patch archiveAt 888=.int (324) from rfl) trivial

private theorem e889 (x : Fin 84 → Rat) : atWire x 889 = atWire x 13 * atWire x 888 := wireStep x (by decide) (show patch archiveAt 889=.mul 13 888 from rfl) ⟨by decide,by decide⟩

private theorem e890 (x : Fin 84 → Rat) : atWire x 890 = atWire x 13 * atWire x 889 := wireStep x (by decide) (show patch archiveAt 890=.mul 13 889 from rfl) ⟨by decide,by decide⟩

private theorem e891 (x : Fin 84 → Rat) : atWire x 891 = atWire x 887 + atWire x 890 := wireStep x (by decide) (show patch archiveAt 891=.add 887 890 from rfl) ⟨by decide,by decide⟩

private theorem e892 (x : Fin 84 → Rat) : atWire x 892 = (1944:Rat) := wireStep x (by decide) (show patch archiveAt 892=.int (1944) from rfl) trivial

private theorem e893 (x : Fin 84 → Rat) : atWire x 893 = atWire x 14 * atWire x 892 := wireStep x (by decide) (show patch archiveAt 893=.mul 14 892 from rfl) ⟨by decide,by decide⟩

private theorem e894 (x : Fin 84 → Rat) : atWire x 894 = atWire x 14 * atWire x 893 := wireStep x (by decide) (show patch archiveAt 894=.mul 14 893 from rfl) ⟨by decide,by decide⟩

private theorem e895 (x : Fin 84 → Rat) : atWire x 895 = atWire x 891 + atWire x 894 := wireStep x (by decide) (show patch archiveAt 895=.add 891 894 from rfl) ⟨by decide,by decide⟩

private theorem e896 (x : Fin 84 → Rat) : atWire x 896 = atWire x 15 * atWire x 149 := wireStep x (by decide) (show patch archiveAt 896=.mul 15 149 from rfl) ⟨by decide,by decide⟩

private theorem e897 (x : Fin 84 → Rat) : atWire x 897 = atWire x 15 * atWire x 896 := wireStep x (by decide) (show patch archiveAt 897=.mul 15 896 from rfl) ⟨by decide,by decide⟩

private theorem e898 (x : Fin 84 → Rat) : atWire x 898 = atWire x 895 + atWire x 897 := wireStep x (by decide) (show patch archiveAt 898=.add 895 897 from rfl) ⟨by decide,by decide⟩

private theorem e899 (x : Fin 84 → Rat) : atWire x 899 = atWire x 307 * atWire x 898 := wireStep x (by decide) (show patch archiveAt 899=.mul 307 898 from rfl) ⟨by decide,by decide⟩

private theorem e900 (x : Fin 84 → Rat) : atWire x 900 = atWire x 306 * atWire x 899 := wireStep x (by decide) (show patch archiveAt 900=.mul 306 899 from rfl) ⟨by decide,by decide⟩

private theorem e901 (x : Fin 84 → Rat) : atWire x 901 = atWire x 885 + atWire x 900 := wireStep x (by decide) (show patch archiveAt 901=.add 885 900 from rfl) ⟨by decide,by decide⟩

private theorem e902 (x : Fin 84 → Rat) : atWire x 902 = (-98304) * H^1 := by
  have raw : atWire x 902 = (-280772121631901826341634990740875623396314546505519646132354689679875582277436488442842937915702424835791365297970692978189911232523148178307203157663832176686034674137735524526281666558106260669160651153258824928587276831536710667969247923067523092914551551163175323475765337035542462464:Rat) :=
    wireStep x (by decide) (show patch archiveAt 902=.int (-280772121631901826341634990740875623396314546505519646132354689679875582277436488442842937915702424835791365297970692978189911232523148178307203157663832176686034674137735524526281666558106260669160651153258824928587276831536710667969247923067523092914551551163175323475765337035542462464) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e903 (x : Fin 84 → Rat) : atWire x 903 = atWire x 9 * atWire x 902 := wireStep x (by decide) (show patch archiveAt 903=.mul 9 902 from rfl) ⟨by decide,by decide⟩

private theorem e904 (x : Fin 84 → Rat) : atWire x 904 = atWire x 9 * atWire x 903 := wireStep x (by decide) (show patch archiveAt 904=.mul 9 903 from rfl) ⟨by decide,by decide⟩

private theorem e905 (x : Fin 84 → Rat) : atWire x 905 = atWire x 399 * atWire x 904 := wireStep x (by decide) (show patch archiveAt 905=.mul 399 904 from rfl) ⟨by decide,by decide⟩

private theorem e906 (x : Fin 84 → Rat) : atWire x 906 = atWire x 305 * atWire x 905 := wireStep x (by decide) (show patch archiveAt 906=.mul 305 905 from rfl) ⟨by decide,by decide⟩

private theorem e907 (x : Fin 84 → Rat) : atWire x 907 = atWire x 301 * atWire x 906 := wireStep x (by decide) (show patch archiveAt 907=.mul 301 906 from rfl) ⟨by decide,by decide⟩

private theorem e908 (x : Fin 84 → Rat) : atWire x 908 = atWire x 300 * atWire x 907 := wireStep x (by decide) (show patch archiveAt 908=.mul 300 907 from rfl) ⟨by decide,by decide⟩

private theorem e909 (x : Fin 84 → Rat) : atWire x 909 = atWire x 901 + atWire x 908 := wireStep x (by decide) (show patch archiveAt 909=.add 901 908 from rfl) ⟨by decide,by decide⟩

private theorem e910 (x : Fin 84 → Rat) : atWire x 910 = (-786432) * H^1 := by
  have raw : atWire x 910 = (-2246176973055214610733079925927004987170516372044157169058837517439004658219491907542743503325619398686330922383765543825519289860185185426457625261310657413488277393101884196210253332464850085353285209226070599428698214652293685343753983384540184743316412409305402587806122696284339699712:Rat) :=
    wireStep x (by decide) (show patch archiveAt 910=.int (-2246176973055214610733079925927004987170516372044157169058837517439004658219491907542743503325619398686330922383765543825519289860185185426457625261310657413488277393101884196210253332464850085353285209226070599428698214652293685343753983384540184743316412409305402587806122696284339699712) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e911 (x : Fin 84 → Rat) : atWire x 911 = atWire x 9 * atWire x 910 := wireStep x (by decide) (show patch archiveAt 911=.mul 9 910 from rfl) ⟨by decide,by decide⟩

private theorem e912 (x : Fin 84 → Rat) : atWire x 912 = atWire x 10 * atWire x 911 := wireStep x (by decide) (show patch archiveAt 912=.mul 10 911 from rfl) ⟨by decide,by decide⟩

private theorem e913 (x : Fin 84 → Rat) : atWire x 913 = atWire x 447 * atWire x 912 := wireStep x (by decide) (show patch archiveAt 913=.mul 447 912 from rfl) ⟨by decide,by decide⟩

private theorem e914 (x : Fin 84 → Rat) : atWire x 914 = atWire x 305 * atWire x 913 := wireStep x (by decide) (show patch archiveAt 914=.mul 305 913 from rfl) ⟨by decide,by decide⟩

private theorem e915 (x : Fin 84 → Rat) : atWire x 915 = atWire x 301 * atWire x 914 := wireStep x (by decide) (show patch archiveAt 915=.mul 301 914 from rfl) ⟨by decide,by decide⟩

private theorem e916 (x : Fin 84 → Rat) : atWire x 916 = atWire x 300 * atWire x 915 := wireStep x (by decide) (show patch archiveAt 916=.mul 300 915 from rfl) ⟨by decide,by decide⟩

private theorem e917 (x : Fin 84 → Rat) : atWire x 917 = atWire x 909 + atWire x 916 := wireStep x (by decide) (show patch archiveAt 917=.add 909 916 from rfl) ⟨by decide,by decide⟩

private theorem e918 (x : Fin 84 → Rat) : atWire x 918 = (-196608) * H^1 := by
  have raw : atWire x 918 = (-561544243263803652683269981481751246792629093011039292264709379359751164554872976885685875831404849671582730595941385956379822465046296356614406315327664353372069348275471049052563333116212521338321302306517649857174553663073421335938495846135046185829103102326350646951530674071084924928:Rat) :=
    wireStep x (by decide) (show patch archiveAt 918=.int (-561544243263803652683269981481751246792629093011039292264709379359751164554872976885685875831404849671582730595941385956379822465046296356614406315327664353372069348275471049052563333116212521338321302306517649857174553663073421335938495846135046185829103102326350646951530674071084924928) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e919 (x : Fin 84 → Rat) : atWire x 919 = atWire x 10 * atWire x 918 := wireStep x (by decide) (show patch archiveAt 919=.mul 10 918 from rfl) ⟨by decide,by decide⟩

private theorem e920 (x : Fin 84 → Rat) : atWire x 920 = atWire x 10 * atWire x 919 := wireStep x (by decide) (show patch archiveAt 920=.mul 10 919 from rfl) ⟨by decide,by decide⟩

private theorem e921 (x : Fin 84 → Rat) : atWire x 921 = atWire x 399 * atWire x 920 := wireStep x (by decide) (show patch archiveAt 921=.mul 399 920 from rfl) ⟨by decide,by decide⟩

private theorem e922 (x : Fin 84 → Rat) : atWire x 922 = atWire x 305 * atWire x 921 := wireStep x (by decide) (show patch archiveAt 922=.mul 305 921 from rfl) ⟨by decide,by decide⟩

private theorem e923 (x : Fin 84 → Rat) : atWire x 923 = atWire x 301 * atWire x 922 := wireStep x (by decide) (show patch archiveAt 923=.mul 301 922 from rfl) ⟨by decide,by decide⟩

private theorem e924 (x : Fin 84 → Rat) : atWire x 924 = atWire x 300 * atWire x 923 := wireStep x (by decide) (show patch archiveAt 924=.mul 300 923 from rfl) ⟨by decide,by decide⟩

private theorem e925 (x : Fin 84 → Rat) : atWire x 925 = atWire x 917 + atWire x 924 := wireStep x (by decide) (show patch archiveAt 925=.add 917 924 from rfl) ⟨by decide,by decide⟩

private theorem e926 (x : Fin 84 → Rat) : atWire x 926 = (-201326592) * H^2 := by
  have raw : atWire x 926 = (-1642353839284989031056853584378246779632920479907769138485103634138784779855211372293225862477874321981492715330160424977741192085969357065390017611381938274925815412641676563766296197866099202691068483591290880282660116843066444856997391650250211265138696004912335901431111664932266538638934710114112718937335324428546520726845616493882373401583320003854837462830983877962154317219302803051383691863165842975375501130555418941119797814644489976186925102613225776789387426174445294066060412266503499978955305151638363150016509519443625706888059127093000192768486958434353152:Rat) :=
    wireStep x (by decide) (show patch archiveAt 926=.int (-1642353839284989031056853584378246779632920479907769138485103634138784779855211372293225862477874321981492715330160424977741192085969357065390017611381938274925815412641676563766296197866099202691068483591290880282660116843066444856997391650250211265138696004912335901431111664932266538638934710114112718937335324428546520726845616493882373401583320003854837462830983877962154317219302803051383691863165842975375501130555418941119797814644489976186925102613225776789387426174445294066060412266503499978955305151638363150016509519443625706888059127093000192768486958434353152) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e927 (x : Fin 84 → Rat) : atWire x 927 = atWire x 9 * atWire x 926 := wireStep x (by decide) (show patch archiveAt 927=.mul 9 926 from rfl) ⟨by decide,by decide⟩

private theorem e928 (x : Fin 84 → Rat) : atWire x 928 = atWire x 9 * atWire x 927 := wireStep x (by decide) (show patch archiveAt 928=.mul 9 927 from rfl) ⟨by decide,by decide⟩

private theorem e929 (x : Fin 84 → Rat) : atWire x 929 = atWire x 9 * atWire x 928 := wireStep x (by decide) (show patch archiveAt 929=.mul 9 928 from rfl) ⟨by decide,by decide⟩

private theorem e930 (x : Fin 84 → Rat) : atWire x 930 = atWire x 9 * atWire x 929 := wireStep x (by decide) (show patch archiveAt 930=.mul 9 929 from rfl) ⟨by decide,by decide⟩

private theorem e931 (x : Fin 84 → Rat) : atWire x 931 = atWire x 399 * atWire x 930 := wireStep x (by decide) (show patch archiveAt 931=.mul 399 930 from rfl) ⟨by decide,by decide⟩

private theorem e932 (x : Fin 84 → Rat) : atWire x 932 = atWire x 399 * atWire x 931 := wireStep x (by decide) (show patch archiveAt 932=.mul 399 931 from rfl) ⟨by decide,by decide⟩

private theorem e933 (x : Fin 84 → Rat) : atWire x 933 = atWire x 307 * atWire x 932 := wireStep x (by decide) (show patch archiveAt 933=.mul 307 932 from rfl) ⟨by decide,by decide⟩

private theorem e934 (x : Fin 84 → Rat) : atWire x 934 = atWire x 306 * atWire x 933 := wireStep x (by decide) (show patch archiveAt 934=.mul 306 933 from rfl) ⟨by decide,by decide⟩

private theorem e935 (x : Fin 84 → Rat) : atWire x 935 = atWire x 925 + atWire x 934 := wireStep x (by decide) (show patch archiveAt 935=.add 925 934 from rfl) ⟨by decide,by decide⟩

private theorem e936 (x : Fin 84 → Rat) : atWire x 936 = (-3221225472) * H^2 := by
  have raw : atWire x 936 = (-26277661428559824496909657350051948474126727678524306215761658146220556477683381956691613799645989151703883445282566799643859073375509713046240281782111012398813046602266825020260739165857587243057095737460654084522561869489063117711958266404003380242219136078597374422897786638916264618222955361825803502997365190856744331629529863902117974425333120061677399405295742047394469075508844848822139069810653487606008018088886703057916765034311839618990801641811612428630198818791124705056966596264055999663284882426213810400264152311098011310208946033488003084295791334949650432:Rat) :=
    wireStep x (by decide) (show patch archiveAt 936=.int (-26277661428559824496909657350051948474126727678524306215761658146220556477683381956691613799645989151703883445282566799643859073375509713046240281782111012398813046602266825020260739165857587243057095737460654084522561869489063117711958266404003380242219136078597374422897786638916264618222955361825803502997365190856744331629529863902117974425333120061677399405295742047394469075508844848822139069810653487606008018088886703057916765034311839618990801641811612428630198818791124705056966596264055999663284882426213810400264152311098011310208946033488003084295791334949650432) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e937 (x : Fin 84 → Rat) : atWire x 937 = atWire x 9 * atWire x 936 := wireStep x (by decide) (show patch archiveAt 937=.mul 9 936 from rfl) ⟨by decide,by decide⟩

private theorem e938 (x : Fin 84 → Rat) : atWire x 938 = atWire x 9 * atWire x 937 := wireStep x (by decide) (show patch archiveAt 938=.mul 9 937 from rfl) ⟨by decide,by decide⟩

private theorem e939 (x : Fin 84 → Rat) : atWire x 939 = atWire x 9 * atWire x 938 := wireStep x (by decide) (show patch archiveAt 939=.mul 9 938 from rfl) ⟨by decide,by decide⟩

private theorem e940 (x : Fin 84 → Rat) : atWire x 940 = atWire x 10 * atWire x 939 := wireStep x (by decide) (show patch archiveAt 940=.mul 10 939 from rfl) ⟨by decide,by decide⟩

private theorem e941 (x : Fin 84 → Rat) : atWire x 941 = atWire x 399 * atWire x 940 := wireStep x (by decide) (show patch archiveAt 941=.mul 399 940 from rfl) ⟨by decide,by decide⟩

private theorem e942 (x : Fin 84 → Rat) : atWire x 942 = atWire x 447 * atWire x 941 := wireStep x (by decide) (show patch archiveAt 942=.mul 447 941 from rfl) ⟨by decide,by decide⟩

private theorem e943 (x : Fin 84 → Rat) : atWire x 943 = atWire x 307 * atWire x 942 := wireStep x (by decide) (show patch archiveAt 943=.mul 307 942 from rfl) ⟨by decide,by decide⟩

private theorem e944 (x : Fin 84 → Rat) : atWire x 944 = atWire x 306 * atWire x 943 := wireStep x (by decide) (show patch archiveAt 944=.mul 306 943 from rfl) ⟨by decide,by decide⟩

private theorem e945 (x : Fin 84 → Rat) : atWire x 945 = atWire x 935 + atWire x 944 := wireStep x (by decide) (show patch archiveAt 945=.add 935 944 from rfl) ⟨by decide,by decide⟩

private theorem e946 (x : Fin 84 → Rat) : atWire x 946 = (-805306368) * H^2 := by
  have raw : atWire x 946 = (-6569415357139956124227414337512987118531681919631076553940414536555139119420845489172903449911497287925970861320641699910964768343877428261560070445527753099703261650566706255065184791464396810764273934365163521130640467372265779427989566601000845060554784019649343605724446659729066154555738840456450875749341297714186082907382465975529493606333280015419349851323935511848617268877211212205534767452663371901502004522221675764479191258577959904747700410452903107157549704697781176264241649066013999915821220606553452600066038077774502827552236508372000771073947833737412608:Rat) :=
    wireStep x (by decide) (show patch archiveAt 946=.int (-6569415357139956124227414337512987118531681919631076553940414536555139119420845489172903449911497287925970861320641699910964768343877428261560070445527753099703261650566706255065184791464396810764273934365163521130640467372265779427989566601000845060554784019649343605724446659729066154555738840456450875749341297714186082907382465975529493606333280015419349851323935511848617268877211212205534767452663371901502004522221675764479191258577959904747700410452903107157549704697781176264241649066013999915821220606553452600066038077774502827552236508372000771073947833737412608) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e947 (x : Fin 84 → Rat) : atWire x 947 = atWire x 9 * atWire x 946 := wireStep x (by decide) (show patch archiveAt 947=.mul 9 946 from rfl) ⟨by decide,by decide⟩

private theorem e948 (x : Fin 84 → Rat) : atWire x 948 = atWire x 9 * atWire x 947 := wireStep x (by decide) (show patch archiveAt 948=.mul 9 947 from rfl) ⟨by decide,by decide⟩

private theorem e949 (x : Fin 84 → Rat) : atWire x 949 = atWire x 10 * atWire x 948 := wireStep x (by decide) (show patch archiveAt 949=.mul 10 948 from rfl) ⟨by decide,by decide⟩

private theorem e950 (x : Fin 84 → Rat) : atWire x 950 = atWire x 10 * atWire x 949 := wireStep x (by decide) (show patch archiveAt 950=.mul 10 949 from rfl) ⟨by decide,by decide⟩

private theorem e951 (x : Fin 84 → Rat) : atWire x 951 = atWire x 399 * atWire x 950 := wireStep x (by decide) (show patch archiveAt 951=.mul 399 950 from rfl) ⟨by decide,by decide⟩

private theorem e952 (x : Fin 84 → Rat) : atWire x 952 = atWire x 399 * atWire x 951 := wireStep x (by decide) (show patch archiveAt 952=.mul 399 951 from rfl) ⟨by decide,by decide⟩

private theorem e953 (x : Fin 84 → Rat) : atWire x 953 = atWire x 307 * atWire x 952 := wireStep x (by decide) (show patch archiveAt 953=.mul 307 952 from rfl) ⟨by decide,by decide⟩

private theorem e954 (x : Fin 84 → Rat) : atWire x 954 = atWire x 306 * atWire x 953 := wireStep x (by decide) (show patch archiveAt 954=.mul 306 953 from rfl) ⟨by decide,by decide⟩

private theorem e955 (x : Fin 84 → Rat) : atWire x 955 = atWire x 945 + atWire x 954 := wireStep x (by decide) (show patch archiveAt 955=.add 945 954 from rfl) ⟨by decide,by decide⟩

private theorem e956 (x : Fin 84 → Rat) : atWire x 956 = (-12884901888) * H^2 := by
  have raw : atWire x 956 = (-105110645714239297987638629400207793896506910714097224863046632584882225910733527826766455198583956606815533781130267198575436293502038852184961127128444049595252186409067300081042956663430348972228382949842616338090247477956252470847833065616013520968876544314389497691591146555665058472891821447303214011989460763426977326518119455608471897701332480246709597621182968189577876302035379395288556279242613950424032072355546812231667060137247358475963206567246449714520795275164498820227866385056223998653139529704855241601056609244392045240835784133952012337183165339798601728:Rat) :=
    wireStep x (by decide) (show patch archiveAt 956=.int (-105110645714239297987638629400207793896506910714097224863046632584882225910733527826766455198583956606815533781130267198575436293502038852184961127128444049595252186409067300081042956663430348972228382949842616338090247477956252470847833065616013520968876544314389497691591146555665058472891821447303214011989460763426977326518119455608471897701332480246709597621182968189577876302035379395288556279242613950424032072355546812231667060137247358475963206567246449714520795275164498820227866385056223998653139529704855241601056609244392045240835784133952012337183165339798601728) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e957 (x : Fin 84 → Rat) : atWire x 957 = atWire x 9 * atWire x 956 := wireStep x (by decide) (show patch archiveAt 957=.mul 9 956 from rfl) ⟨by decide,by decide⟩

private theorem e958 (x : Fin 84 → Rat) : atWire x 958 = atWire x 9 * atWire x 957 := wireStep x (by decide) (show patch archiveAt 958=.mul 9 957 from rfl) ⟨by decide,by decide⟩

private theorem e959 (x : Fin 84 → Rat) : atWire x 959 = atWire x 10 * atWire x 958 := wireStep x (by decide) (show patch archiveAt 959=.mul 10 958 from rfl) ⟨by decide,by decide⟩

private theorem e960 (x : Fin 84 → Rat) : atWire x 960 = atWire x 10 * atWire x 959 := wireStep x (by decide) (show patch archiveAt 960=.mul 10 959 from rfl) ⟨by decide,by decide⟩

private theorem e961 (x : Fin 84 → Rat) : atWire x 961 = atWire x 447 * atWire x 960 := wireStep x (by decide) (show patch archiveAt 961=.mul 447 960 from rfl) ⟨by decide,by decide⟩

private theorem e962 (x : Fin 84 → Rat) : atWire x 962 = atWire x 447 * atWire x 961 := wireStep x (by decide) (show patch archiveAt 962=.mul 447 961 from rfl) ⟨by decide,by decide⟩

private theorem e963 (x : Fin 84 → Rat) : atWire x 963 = atWire x 307 * atWire x 962 := wireStep x (by decide) (show patch archiveAt 963=.mul 307 962 from rfl) ⟨by decide,by decide⟩

private theorem e964 (x : Fin 84 → Rat) : atWire x 964 = atWire x 306 * atWire x 963 := wireStep x (by decide) (show patch archiveAt 964=.mul 306 963 from rfl) ⟨by decide,by decide⟩

private theorem e965 (x : Fin 84 → Rat) : atWire x 965 = atWire x 955 + atWire x 964 := wireStep x (by decide) (show patch archiveAt 965=.add 955 964 from rfl) ⟨by decide,by decide⟩

private theorem e966 (x : Fin 84 → Rat) : atWire x 966 = (-6442450944) * H^2 := by
  have raw : atWire x 966 = (-52555322857119648993819314700103896948253455357048612431523316292441112955366763913383227599291978303407766890565133599287718146751019426092480563564222024797626093204533650040521478331715174486114191474921308169045123738978126235423916532808006760484438272157194748845795573277832529236445910723651607005994730381713488663259059727804235948850666240123354798810591484094788938151017689697644278139621306975212016036177773406115833530068623679237981603283623224857260397637582249410113933192528111999326569764852427620800528304622196022620417892066976006168591582669899300864:Rat) :=
    wireStep x (by decide) (show patch archiveAt 966=.int (-52555322857119648993819314700103896948253455357048612431523316292441112955366763913383227599291978303407766890565133599287718146751019426092480563564222024797626093204533650040521478331715174486114191474921308169045123738978126235423916532808006760484438272157194748845795573277832529236445910723651607005994730381713488663259059727804235948850666240123354798810591484094788938151017689697644278139621306975212016036177773406115833530068623679237981603283623224857260397637582249410113933192528111999326569764852427620800528304622196022620417892066976006168591582669899300864) from rfl) trivial
  rw [raw,H]
  decide +kernel

private theorem e967 (x : Fin 84 → Rat) : atWire x 967 = atWire x 9 * atWire x 966 := wireStep x (by decide) (show patch archiveAt 967=.mul 9 966 from rfl) ⟨by decide,by decide⟩

private theorem e968 (x : Fin 84 → Rat) : atWire x 968 = atWire x 10 * atWire x 967 := wireStep x (by decide) (show patch archiveAt 968=.mul 10 967 from rfl) ⟨by decide,by decide⟩

private theorem e969 (x : Fin 84 → Rat) : atWire x 969 = atWire x 10 * atWire x 968 := wireStep x (by decide) (show patch archiveAt 969=.mul 10 968 from rfl) ⟨by decide,by decide⟩

private theorem e970 (x : Fin 84 → Rat) : atWire x 970 = atWire x 10 * atWire x 969 := wireStep x (by decide) (show patch archiveAt 970=.mul 10 969 from rfl) ⟨by decide,by decide⟩

private theorem e971 (x : Fin 84 → Rat) : atWire x 971 = atWire x 399 * atWire x 970 := wireStep x (by decide) (show patch archiveAt 971=.mul 399 970 from rfl) ⟨by decide,by decide⟩

private theorem e972 (x : Fin 84 → Rat) : atWire x 972 = atWire x 447 * atWire x 971 := wireStep x (by decide) (show patch archiveAt 972=.mul 447 971 from rfl) ⟨by decide,by decide⟩

private theorem e973 (x : Fin 84 → Rat) : atWire x 973 = atWire x 307 * atWire x 972 := wireStep x (by decide) (show patch archiveAt 973=.mul 307 972 from rfl) ⟨by decide,by decide⟩

private theorem e974 (x : Fin 84 → Rat) : atWire x 974 = atWire x 306 * atWire x 973 := wireStep x (by decide) (show patch archiveAt 974=.mul 306 973 from rfl) ⟨by decide,by decide⟩

private theorem e975 (x : Fin 84 → Rat) : atWire x 975 = atWire x 965 + atWire x 974 := wireStep x (by decide) (show patch archiveAt 975=.add 965 974 from rfl) ⟨by decide,by decide⟩

private theorem e976 (x : Fin 84 → Rat) : atWire x 976 = atWire x 10 * atWire x 946 := wireStep x (by decide) (show patch archiveAt 976=.mul 10 946 from rfl) ⟨by decide,by decide⟩

private theorem e977 (x : Fin 84 → Rat) : atWire x 977 = atWire x 10 * atWire x 976 := wireStep x (by decide) (show patch archiveAt 977=.mul 10 976 from rfl) ⟨by decide,by decide⟩

private theorem e978 (x : Fin 84 → Rat) : atWire x 978 = atWire x 10 * atWire x 977 := wireStep x (by decide) (show patch archiveAt 978=.mul 10 977 from rfl) ⟨by decide,by decide⟩

private theorem e979 (x : Fin 84 → Rat) : atWire x 979 = atWire x 10 * atWire x 978 := wireStep x (by decide) (show patch archiveAt 979=.mul 10 978 from rfl) ⟨by decide,by decide⟩

private theorem e980 (x : Fin 84 → Rat) : atWire x 980 = atWire x 399 * atWire x 979 := wireStep x (by decide) (show patch archiveAt 980=.mul 399 979 from rfl) ⟨by decide,by decide⟩

private theorem e981 (x : Fin 84 → Rat) : atWire x 981 = atWire x 399 * atWire x 980 := wireStep x (by decide) (show patch archiveAt 981=.mul 399 980 from rfl) ⟨by decide,by decide⟩

private theorem e982 (x : Fin 84 → Rat) : atWire x 982 = atWire x 307 * atWire x 981 := wireStep x (by decide) (show patch archiveAt 982=.mul 307 981 from rfl) ⟨by decide,by decide⟩

private theorem e983 (x : Fin 84 → Rat) : atWire x 983 = atWire x 306 * atWire x 982 := wireStep x (by decide) (show patch archiveAt 983=.mul 306 982 from rfl) ⟨by decide,by decide⟩

private theorem e984 (x : Fin 84 → Rat) : atWire x 984 = atWire x 975 + atWire x 983 := wireStep x (by decide) (show patch archiveAt 984=.add 975 983 from rfl) ⟨by decide,by decide⟩

theorem divisor_1 (x : Fin 84 → Rat) :
    atWire x 256 = 16*(divisor (rootH x 1)).1 := by
  simp only [e256,e255,e254,e253,e252,e251,e250,e249,e248,e190,e189,e188,e187,e186,e185,e184,e183,e147,e85,e5,e4,h1,divisor,sq,times]
  grobner

theorem divisor_2 (x : Fin 84 → Rat) :
    atWire x 288 = 16*(divisor (rootH x 1)).2 := by
  simp only [e288,e287,e286,e285,e284,e283,e250,e248,e190,e189,e188,e187,e186,e185,e184,e183,e147,e85,e5,e4,h1,divisor,sq,times]
  grobner

theorem ordinate_1 (x : Fin 84 → Rat) :
    atWire x 215 = 4802*(rootJ x 1).1 := by
  simp only [e215,e214,e213,e212,e211,e210,e209,e208,e207,e206,e205,e204,e203,e202,e201,e200,e199,e198,e197,e196,e195,e194,e193,e192,e191,e190,e189,e188,e187,e186,e185,e184,e183,e146,e145,e141,e139,e125,e118,e98,e85,e16,e5,e4,j1,h1,deltaTarget,divDelta,ordinate,PhysicalProjection.Comparison.one,delta,sub,sq,times]
  grobner

theorem ordinate_2 (x : Fin 84 → Rat) :
    atWire x 219 = 4802*(rootJ x 1).2 := by
  simp only [e219,e218,e217,e216,e210,e209,e208,e207,e206,e205,e204,e203,e202,e201,e200,e199,e198,e197,e196,e195,e194,e193,e192,e191,e190,e189,e188,e187,e186,e185,e184,e183,e146,e145,e141,e139,e125,e118,e98,e85,e16,e5,e4,j1,h1,deltaTarget,divDelta,ordinate,PhysicalProjection.Comparison.one,delta,sub,sq,times]
  grobner

theorem numerator_1 (x : Fin 84 → Rat) :
    atWire x 270 = 19208*(numerator (rootH x 1) (rootJ x 1)).1 := by
  simp only [e270,e269,e268,e267,e266,e265,e264,e263,e262,e261,e260,e259,e258,e257,e244,e185,e183,e147,e98,e96,e88,e85,e5,e4,ordinate_1,ordinate_2,h1,numerator,times,sub]
  grobner

theorem numerator_2 (x : Fin 84 → Rat) :
    atWire x 282 = 19208*(numerator (rootH x 1) (rootJ x 1)).2 := by
  simp only [e282,e281,e280,e279,e278,e277,e276,e275,e274,e273,e272,e262,e244,e185,e183,e147,e98,e96,e88,e5,e4,ordinate_1,ordinate_2,h1,numerator,times,sub]
  grobner

theorem norm_wire (x : Fin 84 → Rat) :
    atWire x 299 = 256*norm (divisor (rootH x 1)) := by
  simp only [e299,e298,e297,e296,e148,divisor_1,divisor_2,norm]
  grobner

theorem linear_wire (x : Fin 84 → Rat) :
    linearFactor x = 307328*J*(256*norm (divisor (rootH x 1))) := by
  simp only [e300,e295,linearFactor,norm_wire]
  grobner

theorem quotient_wire (x : Fin 84 → Rat) :
    atWire x 305 = 256*307328*
      (times (numerator (rootH x 1) (rootJ x 1)) (conjugate (divisor (rootH x 1)))).2 := by
  simp only [e305,e304,e303,e302,e293,e289,e98,divisor_1,divisor_2,numerator_1,numerator_2,times,conjugate]
  grobner

theorem product_1 (x : Fin 84 → Rat) :
    atWire x 399 = (productThree x).1 := by
  simp only [e399,e398,e397,e396,e395,e394,e393,e392,e391,e390,e389,e388,e387,e386,e385,e384,e383,e382,e381,e380,e379,e378,e377,e376,e375,e374,e373,e372,e371,e370,e369,e368,e367,e366,e365,e364,e363,e362,e361,e360,e359,e358,e357,e356,e355,e354,e353,e352,e351,e350,e349,e348,e347,e346,e345,e344,e343,e342,e341,e340,e339,e338,e337,e336,e335,e334,e333,e332,e331,e330,e329,e328,e327,e326,e325,e324,e323,e322,e321,e320,e319,e318,e317,e316,e315,e314,e313,e312,e311,e310,e309,e308,e7,e6,e5,e4,e2,e1,productThree,h0,h1,h2,sq,times]
  grobner

theorem product_2 (x : Fin 84 → Rat) :
    2*atWire x 447 = (productThree x).2 := by
  simp only [e447,e446,e445,e444,e443,e442,e441,e440,e439,e438,e437,e436,e435,e434,e433,e432,e431,e430,e429,e428,e427,e426,e425,e424,e423,e422,e421,e420,e419,e418,e417,e416,e415,e414,e413,e412,e411,e410,e409,e408,e407,e406,e405,e404,e403,e402,e401,e400,e390,e389,e388,e376,e375,e374,e371,e370,e369,e368,e367,e351,e350,e345,e344,e337,e336,e333,e332,e331,e324,e323,e318,e317,e316,e315,e313,e312,e311,e310,e309,e308,e7,e6,e5,e4,e2,e1,productThree,h0,h1,h2,sq,times]
  grobner

theorem product_wire (x : Fin 84 → Rat) : firstProduct x = productReal x := by
  simp only [firstProduct,productReal,h3,sq,times]
  have h₁ := product_1 x
  have h₂ := product_2 x
  grobner

theorem homogeneous_row (x : Fin 84 → Rat) :
    atWire x 984 =
      4*((9*linearFactor x*cell x 14)^2+6*(9*linearFactor x*cell x 15)^2
        -2*(linearFactor x*(cell x 16+H))^2
        -3*(atWire x 305+4096*(linearFactor x*H)*firstProduct x)^2
        +2*(linearFactor x*H)^2) := by
  simp only [e984,e983,e982,e981,e980,e979,e978,e977,e976,e975,e974,e973,e972,e971,e970,e969,e968,e967,e966,e965,e964,e963,e962,e961,e960,e959,e958,e957,e956,e955,e954,e953,e952,e951,e950,e949,e948,e947,e946,e945,e944,e943,e942,e941,e940,e939,e938,e937,e936,e935,e934,e933,e932,e931,e930,e929,e928,e927,e926,e925,e924,e923,e922,e921,e920,e919,e918,e917,e916,e915,e914,e913,e912,e911,e910,e909,e908,e907,e906,e905,e904,e903,e902,e901,e900,e899,e898,e897,e896,e895,e894,e893,e892,e891,e890,e889,e888,e887,e886,e885,e884,e307,e306,e301,e243,e149,e15,e14,e13,e10,e9,linearFactor,firstProduct]
  grobner
end AnchorCircuit
