import TriData0
import TriData1
import TriData2
import TriData3
import TriData4
import TriData5
import TriData6
import TriData7
import TriData8
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
def rest (g : Bool) : Rows := [(2,p2),(3,p3),(10,p10),(11,p11),(18,p18),(19,p19),(26,p26),(27,p27),(92,p92),(93,p93),(130,p130),(131,p131),(140,p140),(141,p141),(142,p142),(143,p143),(146,(if g then p146b else p146a)),(147,(if g then p147b else p147a)),(148,p148),(149,p149),(158,p158),(159,p159),(160,p160),(161,p161),(170,p170),(171,p171),(172,p172),(173,p173),(182,p182),(183,p183),(184,(if g then p184b else p184a)),(185,(if g then p185b else p185a)),(188,p188),(189,p189),(192,p192),(193,p193),(196,p196),(197,p197),(207,p207),(208,p208),(209,p209),(210,p210),(211,p211),(212,p212),(213,p213),(214,p214),(302,p302),(304,p304),(335,p335),(337,p337),(339,p339),(352,p352),(354,p354),(385,p385),(387,p387),(389,p389),(404,p404),(435,p435),(437,p437),(439,p439),(474,p474),(475,p475),(492,(if g then p492b else p492a)),(494,p494),(504,p504),(512,(if g then p512b else p512a)),(521,p521),(526,p526),(528,p528),(533,p533),(535,p535),(540,p540),(544,p544),(545,p545),(546,p546),(550,p550),(551,p551),(552,p552),(556,p556),(557,p557),(558,p558),(565,(if g then p565b else p565a)),(673,p673),(674,p674),(677,p677),(678,p678),(681,p681),(682,p682),(685,p685),(686,p686),(700,p700),(701,p701),(702,p702),(703,p703),(704,p704),(705,p705),(706,p706),(707,p707),(708,p708),(709,p709),(710,p710),(711,p711),(712,p712),(713,p713),(714,p714),(715,p715),(716,p716),(717,p717),(718,p718),(719,p719),(720,p720),(721,p721),(722,p722),(723,p723),(724,p724),(725,p725),(726,p726),(727,p727),(728,p728),(729,p729),(730,p730),(731,p731)]
def top : Nat×Polynomial := (402,p402)
def code (i : Nat) : Nat := i-(if 78<i then 1 else 0) - (if 79<i then 1 else 0) - (if 88<i then 1 else 0) - (if 89<i then 1 else 0) - (if 94<i then 1 else 0) - (if 95<i then 1 else 0) - (if 100<i then 1 else 0) - (if 101<i then 1 else 0) - (if 120<i then 1 else 0) - (if 121<i then 1 else 0) - (if 130<i then 1 else 0) - (if 131<i then 1 else 0) - (if 132<i then 1 else 0) - (if 133<i then 1 else 0) - (if 134<i then 1 else 0) - (if 142<i then 1 else 0) - (if 145<i then 1 else 0) - (if 146<i then 1 else 0) - (if 154<i then 1 else 0) - (if 157<i then 1 else 0) - (if 158<i then 1 else 0) - (if 166<i then 1 else 0) - (if 169<i then 1 else 0) - (if 175<i then 1 else 0) - (if 178<i then 1 else 0) - (if 179<i then 1 else 0) - (if 180<i then 1 else 0) - (if 181<i then 1 else 0) - (if 182<i then 1 else 0) - (if 183<i then 1 else 0) - (if 184<i then 1 else 0) - (if 185<i then 1 else 0) - (if 186<i then 1 else 0) - (if 187<i then 1 else 0) - (if 188<i then 1 else 0) - (if 189<i then 1 else 0) - (if 190<i then 1 else 0) - (if 191<i then 1 else 0) - (if 192<i then 1 else 0) - (if 193<i then 1 else 0) - (if 194<i then 1 else 0) - (if 195<i then 1 else 0) - (if 196<i then 1 else 0) - (if 197<i then 1 else 0) - (if 198<i then 1 else 0) - (if 199<i then 1 else 0) - (if 200<i then 1 else 0) - (if 201<i then 1 else 0) - (if 202<i then 1 else 0) - (if 203<i then 1 else 0) - (if 204<i then 1 else 0) - (if 205<i then 1 else 0) - (if 206<i then 1 else 0) - (if 207<i then 1 else 0) - (if 208<i then 1 else 0) - (if 209<i then 1 else 0) - (if 210<i then 1 else 0) - (if 211<i then 1 else 0) - (if 212<i then 1 else 0) - (if 213<i then 1 else 0) - (if 214<i then 1 else 0) - (if 215<i then 1 else 0) - (if 216<i then 1 else 0) - (if 217<i then 1 else 0) - (if 218<i then 1 else 0) - (if 219<i then 1 else 0) - (if 220<i then 1 else 0) - (if 221<i then 1 else 0) - (if 222<i then 1 else 0) - (if 223<i then 1 else 0) - (if 224<i then 1 else 0) - (if 225<i then 1 else 0) - (if 226<i then 1 else 0)
def back (i : Nat) : Nat := i+(if 77<i then 1 else 0) + (if 77<i then 1 else 0) + (if 85<i then 1 else 0) + (if 85<i then 1 else 0) + (if 89<i then 1 else 0) + (if 89<i then 1 else 0) + (if 93<i then 1 else 0) + (if 93<i then 1 else 0) + (if 111<i then 1 else 0) + (if 111<i then 1 else 0) + (if 119<i then 1 else 0) + (if 119<i then 1 else 0) + (if 119<i then 1 else 0) + (if 119<i then 1 else 0) + (if 119<i then 1 else 0) + (if 126<i then 1 else 0) + (if 128<i then 1 else 0) + (if 128<i then 1 else 0) + (if 135<i then 1 else 0) + (if 137<i then 1 else 0) + (if 137<i then 1 else 0) + (if 144<i then 1 else 0) + (if 146<i then 1 else 0) + (if 151<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0) + (if 153<i then 1 else 0)
def tail73 (_ : Bool) : List Pivot := []
def tail72 (g : Bool) := p684 :: tail73 g
def tail71 (g : Bool) := p683 :: tail72 g
def tail70 (g : Bool) := p680 :: tail71 g
def tail69 (g : Bool) := p679 :: tail70 g
def tail68 (g : Bool) := p564 :: tail69 g
def tail67 (g : Bool) := (if g then p560b else p560a) :: tail68 g
def tail66 (g : Bool) := p453 :: tail67 g
def tail65 (g : Bool) := p658 :: tail66 g
def tail64 (g : Bool) := p656 :: tail65 g
def tail63 (g : Bool) := p657 :: tail64 g
def tail62 (g : Bool) := p648 :: tail63 g
def tail61 (g : Bool) := p647 :: tail62 g
def tail60 (g : Bool) := p646 :: tail61 g
def tail59 (g : Bool) := p645 :: tail60 g
def tail58 (g : Bool) := p642 :: tail59 g
def tail57 (g : Bool) := p641 :: tail58 g
def tail56 (g : Bool) := p414 :: tail57 g
def tail55 (g : Bool) := p655 :: tail56 g
def tail54 (g : Bool) := p654 :: tail55 g
def tail53 (g : Bool) := p653 :: tail54 g
def tail52 (g : Bool) := p399 :: tail53 g
def tail51 (g : Bool) := p395 :: tail52 g
def tail50 (g : Bool) := p297 :: tail51 g
def tail49 (g : Bool) := p296 :: tail50 g
def tail48 (g : Bool) := p636 :: tail49 g
def tail47 (g : Bool) := p634 :: tail48 g
def tail46 (g : Bool) := p635 :: tail47 g
def tail45 (g : Bool) := p626 :: tail46 g
def tail44 (g : Bool) := p625 :: tail45 g
def tail43 (g : Bool) := p624 :: tail44 g
def tail42 (g : Bool) := p623 :: tail43 g
def tail41 (g : Bool) := p620 :: tail42 g
def tail40 (g : Bool) := p619 :: tail41 g
def tail39 (g : Bool) := p364 :: tail40 g
def tail38 (g : Bool) := p633 :: tail39 g
def tail37 (g : Bool) := p632 :: tail38 g
def tail36 (g : Bool) := p631 :: tail37 g
def tail35 (g : Bool) := p350 :: tail36 g
def tail34 (g : Bool) := p345 :: tail35 g
def tail33 (g : Bool) := p295 :: tail34 g
def tail32 (g : Bool) := p292 :: tail33 g
def tail31 (g : Bool) := p291 :: tail32 g
def tail30 (g : Bool) := p614 :: tail31 g
def tail29 (g : Bool) := p612 :: tail30 g
def tail28 (g : Bool) := p613 :: tail29 g
def tail27 (g : Bool) := p586 :: tail28 g
def tail26 (g : Bool) := p585 :: tail27 g
def tail25 (g : Bool) := p604 :: tail26 g
def tail24 (g : Bool) := p603 :: tail25 g
def tail23 (g : Bool) := p151 :: tail24 g
def tail22 (g : Bool) := p150 :: tail23 g
def tail21 (g : Bool) := p602 :: tail22 g
def tail20 (g : Bool) := p580 :: tail21 g
def tail19 (g : Bool) := p581 :: tail20 g
def tail18 (g : Bool) := p601 :: tail19 g
def tail17 (g : Bool) := p133 :: tail18 g
def tail16 (g : Bool) := p132 :: tail17 g
def tail15 (g : Bool) := p598 :: tail16 g
def tail14 (g : Bool) := p568 :: tail15 g
def tail13 (g : Bool) := p569 :: tail14 g
def tail12 (g : Bool) := p597 :: tail13 g
def tail11 (g : Bool) := p314 :: tail12 g
def tail10 (g : Bool) := p611 :: tail11 g
def tail9 (g : Bool) := p588 :: tail10 g
def tail8 (g : Bool) := p587 :: tail9 g
def tail7 (g : Bool) := p610 :: tail8 g
def tail6 (g : Bool) := p609 :: tail7 g
def tail5 (g : Bool) := p592 :: tail6 g
def tail4 (g : Bool) := p590 :: tail5 g
def tail3 (g : Bool) := p511 :: tail4 g
def tail2 (g : Bool) := p591 :: tail3 g
def tail1 (g : Bool) := p206 :: tail2 g
def tail0 (g : Bool) := p205 :: tail1 g
def ps := tail0
def w (i : Nat) : Int := if inside i then if i=32 then (1:Int) else if i=178 then (197769848042768400000000:Int) else if i=179 then (1529819947298299936610017206298061877288175236769780537806873600000000000000000000000000000000:Int) else if i=191 then (1:Int) else if i=193 then (1:Int) else if i=195 then (1:Int) else if i=197 then (1:Int) else if i=199 then (1:Int) else if i=201 then (1:Int) else if i=203 then (1:Int) else if i=205 then (1:Int) else if i=207 then (1:Int) else if i=209 then (1:Int) else if i=211 then (1:Int) else if i=213 then (1:Int) else if i=215 then (1:Int) else if i=217 then (1:Int) else if i=219 then (1:Int) else if i=221 then (1:Int) else if i=223 then (1:Int) else if i=225 then (1:Int) else 0 else 0
end Triangular.Data
