import PDSharedData
namespace ProjectionDescent.Gate510
open Shared
def parent : Rows := table parentIds (original false)
def compact : Rows := table stepI15 (fun i => renumber code (stepF15 false i))
end ProjectionDescent.Gate510
