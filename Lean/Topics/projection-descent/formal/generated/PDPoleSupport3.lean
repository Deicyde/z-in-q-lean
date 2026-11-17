import PDSharedData
import ChunkSupport
namespace ProjectionDescent.Shared
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
private def part0 : List Nat := [2,3,10,11,18,19,24,25,26,27,92,93]
private theorem check0 (g : Bool) : checkRows part0 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part1 : List Nat := [130]
private theorem check1 (g : Bool) : checkRows part1 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part2 : List Nat := [131,132,133]
private theorem check2 (g : Bool) : checkRows part2 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part3 : List Nat := [140,141,142]
private theorem check3 (g : Bool) : checkRows part3 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part4 : List Nat := [143,146,147,148]
private theorem check4 (g : Bool) : checkRows part4 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part5 : List Nat := [149,150,151,158,159,160,161,170,171,172]
private theorem check5 (g : Bool) : checkRows part5 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part6 : List Nat := [173,182,183,184,185,188,189,192,193,196,197]
private theorem check6 (g : Bool) : checkRows part6 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part7 : List Nat := [205,206]
private theorem check7 (g : Bool) : checkRows part7 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part8 : List Nat := [207,208,209,210,211]
private theorem check8 (g : Bool) : checkRows part8 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part9 : List Nat := [212,213,214,289,290,291,292,295,296,297,298]
private theorem check9 (g : Bool) : checkRows part9 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part10 : List Nat := [302,304,314,335,337,339,345,346,350,352]
private theorem check10 (g : Bool) : checkRows part10 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part11 : List Nat := [354,363,364,385,387,389,395,396,399]
private theorem check11 (g : Bool) : checkRows part11 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part12 : List Nat := [401]
private theorem check12 (g : Bool) : checkRows part12 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part13 : List Nat := [402]
private theorem check13 (g : Bool) : checkRows part13 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part14 : List Nat := [404,414,435,437,453,474]
private theorem check14 (g : Bool) : checkRows part14 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part15 : List Nat := [475,492,494,499,502,504,511]
private theorem check15 (g : Bool) : checkRows part15 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part16 : List Nat := [512,513,514,520,521,526,528,533,534,535,540,544]
private theorem check16 (g : Bool) : checkRows part16 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part17 : List Nat := [545,546,550,551,552,556,557,558,560,564,565,568]
private theorem check17 (g : Bool) : checkRows part17 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part18 : List Nat := [569,580,581,585,586]
private theorem check18 (g : Bool) : checkRows part18 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part19 : List Nat := [587]
private theorem check19 (g : Bool) : checkRows part19 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part20 : List Nat := [588]
private theorem check20 (g : Bool) : checkRows part20 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part21 : List Nat := [590]
private theorem check21 (g : Bool) : checkRows part21 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part22 : List Nat := [591]
private theorem check22 (g : Bool) : checkRows part22 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part23 : List Nat := [592,593]
private theorem check23 (g : Bool) : checkRows part23 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part24 : List Nat := [594,597,598]
private theorem check24 (g : Bool) : checkRows part24 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part25 : List Nat := [601]
private theorem check25 (g : Bool) : checkRows part25 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part26 : List Nat := [602]
private theorem check26 (g : Bool) : checkRows part26 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part27 : List Nat := [603]
private theorem check27 (g : Bool) : checkRows part27 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part28 : List Nat := [604]
private theorem check28 (g : Bool) : checkRows part28 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part29 : List Nat := [609,610]
private theorem check29 (g : Bool) : checkRows part29 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part30 : List Nat := [611]
private theorem check30 (g : Bool) : checkRows part30 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part31 : List Nat := [612,613]
private theorem check31 (g : Bool) : checkRows part31 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part32 : List Nat := [614,619,620]
private theorem check32 (g : Bool) : checkRows part32 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part33 : List Nat := [623]
private theorem check33 (g : Bool) : checkRows part33 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part34 : List Nat := [624]
private theorem check34 (g : Bool) : checkRows part34 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part35 : List Nat := [625]
private theorem check35 (g : Bool) : checkRows part35 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part36 : List Nat := [626]
private theorem check36 (g : Bool) : checkRows part36 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part37 : List Nat := [631,632]
private theorem check37 (g : Bool) : checkRows part37 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part38 : List Nat := [633]
private theorem check38 (g : Bool) : checkRows part38 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part39 : List Nat := [634,635]
private theorem check39 (g : Bool) : checkRows part39 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part40 : List Nat := [636,641,642]
private theorem check40 (g : Bool) : checkRows part40 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part41 : List Nat := [645]
private theorem check41 (g : Bool) : checkRows part41 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part42 : List Nat := [646]
private theorem check42 (g : Bool) : checkRows part42 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part43 : List Nat := [647]
private theorem check43 (g : Bool) : checkRows part43 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part44 : List Nat := [648]
private theorem check44 (g : Bool) : checkRows part44 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part45 : List Nat := [653,654]
private theorem check45 (g : Bool) : checkRows part45 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part46 : List Nat := [655]
private theorem check46 (g : Bool) : checkRows part46 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part47 : List Nat := [656,657]
private theorem check47 (g : Bool) : checkRows part47 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part48 : List Nat := [658,673]
private theorem check48 (g : Bool) : checkRows part48 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part49 : List Nat := [674,677]
private theorem check49 (g : Bool) : checkRows part49 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part50 : List Nat := [678,679,680]
private theorem check50 (g : Bool) : checkRows part50 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part51 : List Nat := [681]
private theorem check51 (g : Bool) : checkRows part51 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part52 : List Nat := [682,683,684]
private theorem check52 (g : Bool) : checkRows part52 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part53 : List Nat := [685]
private theorem check53 (g : Bool) : checkRows part53 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part54 : List Nat := [686,700]
private theorem check54 (g : Bool) : checkRows part54 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part55 : List Nat := [701,702,703]
private theorem check55 (g : Bool) : checkRows part55 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part56 : List Nat := [704,705,706,707]
private theorem check56 (g : Bool) : checkRows part56 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part57 : List Nat := [708,709,710]
private theorem check57 (g : Bool) : checkRows part57 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part58 : List Nat := [711,712,713,714]
private theorem check58 (g : Bool) : checkRows part58 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part59 : List Nat := [715,716,717]
private theorem check59 (g : Bool) : checkRows part59 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part60 : List Nat := [718,719,720,721]
private theorem check60 (g : Bool) : checkRows part60 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part61 : List Nat := [722,723,724,725]
private theorem check61 (g : Bool) : checkRows part61 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part62 : List Nat := [726,727,728,729]
private theorem check62 (g : Bool) : checkRows part62 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part63 : List Nat := [730,731]
private theorem check63 (g : Bool) : checkRows part63 (poleF2 g) (apart [43,44,188,45,46])=true := by
  cases g <;> decide
private def part64 := part0 ++ part1
private theorem check64 (g : Bool) : checkRows part64 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part0 part1 (poleF2 g) (apart [43,44,188,45,46]) (check0 g) (check1 g)
private def part65 := part2 ++ part3
private theorem check65 (g : Bool) : checkRows part65 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part2 part3 (poleF2 g) (apart [43,44,188,45,46]) (check2 g) (check3 g)
private def part66 := part4 ++ part5
private theorem check66 (g : Bool) : checkRows part66 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part4 part5 (poleF2 g) (apart [43,44,188,45,46]) (check4 g) (check5 g)
private def part67 := part6 ++ part7
private theorem check67 (g : Bool) : checkRows part67 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part6 part7 (poleF2 g) (apart [43,44,188,45,46]) (check6 g) (check7 g)
private def part68 := part8 ++ part9
private theorem check68 (g : Bool) : checkRows part68 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part8 part9 (poleF2 g) (apart [43,44,188,45,46]) (check8 g) (check9 g)
private def part69 := part10 ++ part11
private theorem check69 (g : Bool) : checkRows part69 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part10 part11 (poleF2 g) (apart [43,44,188,45,46]) (check10 g) (check11 g)
private def part70 := part12 ++ part13
private theorem check70 (g : Bool) : checkRows part70 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part12 part13 (poleF2 g) (apart [43,44,188,45,46]) (check12 g) (check13 g)
private def part71 := part14 ++ part15
private theorem check71 (g : Bool) : checkRows part71 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part14 part15 (poleF2 g) (apart [43,44,188,45,46]) (check14 g) (check15 g)
private def part72 := part16 ++ part17
private theorem check72 (g : Bool) : checkRows part72 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part16 part17 (poleF2 g) (apart [43,44,188,45,46]) (check16 g) (check17 g)
private def part73 := part18 ++ part19
private theorem check73 (g : Bool) : checkRows part73 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part18 part19 (poleF2 g) (apart [43,44,188,45,46]) (check18 g) (check19 g)
private def part74 := part20 ++ part21
private theorem check74 (g : Bool) : checkRows part74 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part20 part21 (poleF2 g) (apart [43,44,188,45,46]) (check20 g) (check21 g)
private def part75 := part22 ++ part23
private theorem check75 (g : Bool) : checkRows part75 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part22 part23 (poleF2 g) (apart [43,44,188,45,46]) (check22 g) (check23 g)
private def part76 := part24 ++ part25
private theorem check76 (g : Bool) : checkRows part76 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part24 part25 (poleF2 g) (apart [43,44,188,45,46]) (check24 g) (check25 g)
private def part77 := part26 ++ part27
private theorem check77 (g : Bool) : checkRows part77 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part26 part27 (poleF2 g) (apart [43,44,188,45,46]) (check26 g) (check27 g)
private def part78 := part28 ++ part29
private theorem check78 (g : Bool) : checkRows part78 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part28 part29 (poleF2 g) (apart [43,44,188,45,46]) (check28 g) (check29 g)
private def part79 := part30 ++ part31
private theorem check79 (g : Bool) : checkRows part79 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part30 part31 (poleF2 g) (apart [43,44,188,45,46]) (check30 g) (check31 g)
private def part80 := part32 ++ part33
private theorem check80 (g : Bool) : checkRows part80 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part32 part33 (poleF2 g) (apart [43,44,188,45,46]) (check32 g) (check33 g)
private def part81 := part34 ++ part35
private theorem check81 (g : Bool) : checkRows part81 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part34 part35 (poleF2 g) (apart [43,44,188,45,46]) (check34 g) (check35 g)
private def part82 := part36 ++ part37
private theorem check82 (g : Bool) : checkRows part82 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part36 part37 (poleF2 g) (apart [43,44,188,45,46]) (check36 g) (check37 g)
private def part83 := part38 ++ part39
private theorem check83 (g : Bool) : checkRows part83 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part38 part39 (poleF2 g) (apart [43,44,188,45,46]) (check38 g) (check39 g)
private def part84 := part40 ++ part41
private theorem check84 (g : Bool) : checkRows part84 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part40 part41 (poleF2 g) (apart [43,44,188,45,46]) (check40 g) (check41 g)
private def part85 := part42 ++ part43
private theorem check85 (g : Bool) : checkRows part85 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part42 part43 (poleF2 g) (apart [43,44,188,45,46]) (check42 g) (check43 g)
private def part86 := part44 ++ part45
private theorem check86 (g : Bool) : checkRows part86 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part44 part45 (poleF2 g) (apart [43,44,188,45,46]) (check44 g) (check45 g)
private def part87 := part46 ++ part47
private theorem check87 (g : Bool) : checkRows part87 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part46 part47 (poleF2 g) (apart [43,44,188,45,46]) (check46 g) (check47 g)
private def part88 := part48 ++ part49
private theorem check88 (g : Bool) : checkRows part88 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part48 part49 (poleF2 g) (apart [43,44,188,45,46]) (check48 g) (check49 g)
private def part89 := part50 ++ part51
private theorem check89 (g : Bool) : checkRows part89 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part50 part51 (poleF2 g) (apart [43,44,188,45,46]) (check50 g) (check51 g)
private def part90 := part52 ++ part53
private theorem check90 (g : Bool) : checkRows part90 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part52 part53 (poleF2 g) (apart [43,44,188,45,46]) (check52 g) (check53 g)
private def part91 := part54 ++ part55
private theorem check91 (g : Bool) : checkRows part91 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part54 part55 (poleF2 g) (apart [43,44,188,45,46]) (check54 g) (check55 g)
private def part92 := part56 ++ part57
private theorem check92 (g : Bool) : checkRows part92 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part56 part57 (poleF2 g) (apart [43,44,188,45,46]) (check56 g) (check57 g)
private def part93 := part58 ++ part59
private theorem check93 (g : Bool) : checkRows part93 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part58 part59 (poleF2 g) (apart [43,44,188,45,46]) (check58 g) (check59 g)
private def part94 := part60 ++ part61
private theorem check94 (g : Bool) : checkRows part94 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part60 part61 (poleF2 g) (apart [43,44,188,45,46]) (check60 g) (check61 g)
private def part95 := part62 ++ part63
private theorem check95 (g : Bool) : checkRows part95 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part62 part63 (poleF2 g) (apart [43,44,188,45,46]) (check62 g) (check63 g)
private def part96 := part64 ++ part65
private theorem check96 (g : Bool) : checkRows part96 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part64 part65 (poleF2 g) (apart [43,44,188,45,46]) (check64 g) (check65 g)
private def part97 := part66 ++ part67
private theorem check97 (g : Bool) : checkRows part97 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part66 part67 (poleF2 g) (apart [43,44,188,45,46]) (check66 g) (check67 g)
private def part98 := part68 ++ part69
private theorem check98 (g : Bool) : checkRows part98 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part68 part69 (poleF2 g) (apart [43,44,188,45,46]) (check68 g) (check69 g)
private def part99 := part70 ++ part71
private theorem check99 (g : Bool) : checkRows part99 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part70 part71 (poleF2 g) (apart [43,44,188,45,46]) (check70 g) (check71 g)
private def part100 := part72 ++ part73
private theorem check100 (g : Bool) : checkRows part100 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part72 part73 (poleF2 g) (apart [43,44,188,45,46]) (check72 g) (check73 g)
private def part101 := part74 ++ part75
private theorem check101 (g : Bool) : checkRows part101 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part74 part75 (poleF2 g) (apart [43,44,188,45,46]) (check74 g) (check75 g)
private def part102 := part76 ++ part77
private theorem check102 (g : Bool) : checkRows part102 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part76 part77 (poleF2 g) (apart [43,44,188,45,46]) (check76 g) (check77 g)
private def part103 := part78 ++ part79
private theorem check103 (g : Bool) : checkRows part103 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part78 part79 (poleF2 g) (apart [43,44,188,45,46]) (check78 g) (check79 g)
private def part104 := part80 ++ part81
private theorem check104 (g : Bool) : checkRows part104 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part80 part81 (poleF2 g) (apart [43,44,188,45,46]) (check80 g) (check81 g)
private def part105 := part82 ++ part83
private theorem check105 (g : Bool) : checkRows part105 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part82 part83 (poleF2 g) (apart [43,44,188,45,46]) (check82 g) (check83 g)
private def part106 := part84 ++ part85
private theorem check106 (g : Bool) : checkRows part106 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part84 part85 (poleF2 g) (apart [43,44,188,45,46]) (check84 g) (check85 g)
private def part107 := part86 ++ part87
private theorem check107 (g : Bool) : checkRows part107 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part86 part87 (poleF2 g) (apart [43,44,188,45,46]) (check86 g) (check87 g)
private def part108 := part88 ++ part89
private theorem check108 (g : Bool) : checkRows part108 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part88 part89 (poleF2 g) (apart [43,44,188,45,46]) (check88 g) (check89 g)
private def part109 := part90 ++ part91
private theorem check109 (g : Bool) : checkRows part109 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part90 part91 (poleF2 g) (apart [43,44,188,45,46]) (check90 g) (check91 g)
private def part110 := part92 ++ part93
private theorem check110 (g : Bool) : checkRows part110 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part92 part93 (poleF2 g) (apart [43,44,188,45,46]) (check92 g) (check93 g)
private def part111 := part94 ++ part95
private theorem check111 (g : Bool) : checkRows part111 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part94 part95 (poleF2 g) (apart [43,44,188,45,46]) (check94 g) (check95 g)
private def part112 := part96 ++ part97
private theorem check112 (g : Bool) : checkRows part112 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part96 part97 (poleF2 g) (apart [43,44,188,45,46]) (check96 g) (check97 g)
private def part113 := part98 ++ part99
private theorem check113 (g : Bool) : checkRows part113 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part98 part99 (poleF2 g) (apart [43,44,188,45,46]) (check98 g) (check99 g)
private def part114 := part100 ++ part101
private theorem check114 (g : Bool) : checkRows part114 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part100 part101 (poleF2 g) (apart [43,44,188,45,46]) (check100 g) (check101 g)
private def part115 := part102 ++ part103
private theorem check115 (g : Bool) : checkRows part115 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part102 part103 (poleF2 g) (apart [43,44,188,45,46]) (check102 g) (check103 g)
private def part116 := part104 ++ part105
private theorem check116 (g : Bool) : checkRows part116 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part104 part105 (poleF2 g) (apart [43,44,188,45,46]) (check104 g) (check105 g)
private def part117 := part106 ++ part107
private theorem check117 (g : Bool) : checkRows part117 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part106 part107 (poleF2 g) (apart [43,44,188,45,46]) (check106 g) (check107 g)
private def part118 := part108 ++ part109
private theorem check118 (g : Bool) : checkRows part118 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part108 part109 (poleF2 g) (apart [43,44,188,45,46]) (check108 g) (check109 g)
private def part119 := part110 ++ part111
private theorem check119 (g : Bool) : checkRows part119 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part110 part111 (poleF2 g) (apart [43,44,188,45,46]) (check110 g) (check111 g)
private def part120 := part112 ++ part113
private theorem check120 (g : Bool) : checkRows part120 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part112 part113 (poleF2 g) (apart [43,44,188,45,46]) (check112 g) (check113 g)
private def part121 := part114 ++ part115
private theorem check121 (g : Bool) : checkRows part121 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part114 part115 (poleF2 g) (apart [43,44,188,45,46]) (check114 g) (check115 g)
private def part122 := part116 ++ part117
private theorem check122 (g : Bool) : checkRows part122 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part116 part117 (poleF2 g) (apart [43,44,188,45,46]) (check116 g) (check117 g)
private def part123 := part118 ++ part119
private theorem check123 (g : Bool) : checkRows part123 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part118 part119 (poleF2 g) (apart [43,44,188,45,46]) (check118 g) (check119 g)
private def part124 := part120 ++ part121
private theorem check124 (g : Bool) : checkRows part124 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part120 part121 (poleF2 g) (apart [43,44,188,45,46]) (check120 g) (check121 g)
private def part125 := part122 ++ part123
private theorem check125 (g : Bool) : checkRows part125 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part122 part123 (poleF2 g) (apart [43,44,188,45,46]) (check122 g) (check123 g)
private def part126 := part124 ++ part125
private theorem check126 (g : Bool) : checkRows part126 (poleF2 g) (apart [43,44,188,45,46])=true :=
  join_checks part124 part125 (poleF2 g) (apart [43,44,188,45,46]) (check124 g) (check125 g)
theorem outside3 (g : Bool) : ∀ i∈(removeId 439 (removeId 444 (removeId 441 poleI2))), supported (apart [43,44,188,45,46]) (poleF2 g i) := by
  have exactIds : (removeId 439 (removeId 444 (removeId 441 poleI2)))=part126 := by decide
  rw [exactIds]; exact checked_support (check126 g)
end ProjectionDescent.Shared
