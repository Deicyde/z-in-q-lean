import PDOriginal0
import PDOriginal1
import PDOriginal2
import PDOriginal3
import PDOriginal4
import PDOriginal5
import PDOriginal6
import PDOriginal7

open ZeroInput.Sparse
namespace ProjectionDescent.Shared


def parentIds : List Nat := [2,3,10,11,18,19,24,25,26,27,92,93,130,131,132,133,140,141,142,143,146,147,148,149,150,151,158,159,160,161,170,171,172,173,182,183,184,185,188,189,192,193,196,197,205,206,207,208,209,210,211,212,213,214,289,290,291,292,295,296,297,298,302,304,314,335,337,339,341,344,345,346,350,352,354,363,364,385,387,389,391,394,395,396,399,401,402,404,414,435,437,439,441,444,453,474,475,492,494,499,502,504,511,512,513,514,520,521,526,528,533,534,535,540,544,545,546,550,551,552,556,557,558,560,564,565,568,569,580,581,585,586,587,588,590,591,592,593,594,597,598,601,602,603,604,609,610,611,612,613,614,619,620,623,624,625,626,631,632,633,634,635,636,641,642,645,646,647,648,653,654,655,656,657,658,673,674,677,678,679,680,681,682,683,684,685,686,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731]

def original (g : Bool) (i : Nat) : Polynomial :=
  (if i < 528 then (if i < 289 then (if i < 159 then (if i < 131 then (if i < 24 then (if i < 11 then (if i < 3 then (if i=2 then p2 else []) else (if i < 10 then (if i=3 then p3 else []) else (if i=10 then p10 else []))) else (if i < 18 then (if i=11 then p11 else []) else (if i < 19 then (if i=18 then p18 else []) else (if i=19 then p19 else [])))) else (if i < 27 then (if i < 25 then (if i=24 then p24 else []) else (if i < 26 then (if i=25 then p25 else []) else (if i=26 then p26 else []))) else (if i < 93 then (if i < 92 then (if i=27 then p27 else []) else (if i=92 then p92 else [])) else (if i < 130 then (if i=93 then p93 else []) else (if i=130 then p130 else []))))) else (if i < 146 then (if i < 140 then (if i < 132 then (if i=131 then p131 else []) else (if i < 133 then (if i=132 then p132 else []) else (if i=133 then p133 else []))) else (if i < 142 then (if i < 141 then (if i=140 then p140 else []) else (if i=141 then p141 else [])) else (if i < 143 then (if i=142 then p142 else []) else (if i=143 then p143 else [])))) else (if i < 149 then (if i < 147 then (if i=146 then (if g then p146b else p146a) else []) else (if i < 148 then (if i=147 then (if g then p147b else p147a) else []) else (if i=148 then p148 else []))) else (if i < 151 then (if i < 150 then (if i=149 then p149 else []) else (if i=150 then p150 else [])) else (if i < 158 then (if i=151 then p151 else []) else (if i=158 then p158 else [])))))) else (if i < 192 then (if i < 173 then (if i < 170 then (if i < 160 then (if i=159 then p159 else []) else (if i < 161 then (if i=160 then p160 else []) else (if i=161 then p161 else []))) else (if i < 171 then (if i=170 then p170 else []) else (if i < 172 then (if i=171 then p171 else []) else (if i=172 then p172 else [])))) else (if i < 184 then (if i < 182 then (if i=173 then p173 else []) else (if i < 183 then (if i=182 then p182 else []) else (if i=183 then p183 else []))) else (if i < 188 then (if i < 185 then (if i=184 then (if g then p184b else p184a) else []) else (if i=185 then (if g then p185b else p185a) else [])) else (if i < 189 then (if i=188 then p188 else []) else (if i=189 then p189 else []))))) else (if i < 208 then (if i < 197 then (if i < 193 then (if i=192 then p192 else []) else (if i < 196 then (if i=193 then p193 else []) else (if i=196 then p196 else []))) else (if i < 206 then (if i < 205 then (if i=197 then p197 else []) else (if i=205 then p205 else [])) else (if i < 207 then (if i=206 then p206 else []) else (if i=207 then p207 else [])))) else (if i < 211 then (if i < 209 then (if i=208 then p208 else []) else (if i < 210 then (if i=209 then p209 else []) else (if i=210 then p210 else []))) else (if i < 213 then (if i < 212 then (if i=211 then p211 else []) else (if i=212 then p212 else [])) else (if i < 214 then (if i=213 then p213 else []) else (if i=214 then p214 else []))))))) else (if i < 394 then (if i < 339 then (if i < 297 then (if i < 292 then (if i < 290 then (if i=289 then p289 else []) else (if i < 291 then (if i=290 then p290 else []) else (if i=291 then p291 else []))) else (if i < 295 then (if i=292 then p292 else []) else (if i < 296 then (if i=295 then p295 else []) else (if i=296 then p296 else [])))) else (if i < 304 then (if i < 298 then (if i=297 then p297 else []) else (if i < 302 then (if i=298 then p298 else []) else (if i=302 then p302 else []))) else (if i < 335 then (if i < 314 then (if i=304 then p304 else []) else (if i=314 then p314 else [])) else (if i < 337 then (if i=335 then p335 else []) else (if i=337 then p337 else []))))) else (if i < 354 then (if i < 345 then (if i < 341 then (if i=339 then p339 else []) else (if i < 344 then (if i=341 then p341 else []) else (if i=344 then p344 else []))) else (if i < 350 then (if i < 346 then (if i=345 then p345 else []) else (if i=346 then p346 else [])) else (if i < 352 then (if i=350 then p350 else []) else (if i=352 then p352 else [])))) else (if i < 385 then (if i < 363 then (if i=354 then p354 else []) else (if i < 364 then (if i=363 then p363 else []) else (if i=364 then p364 else []))) else (if i < 389 then (if i < 387 then (if i=385 then p385 else []) else (if i=387 then p387 else [])) else (if i < 391 then (if i=389 then p389 else []) else (if i=391 then p391 else [])))))) else (if i < 474 then (if i < 414 then (if i < 399 then (if i < 395 then (if i=394 then p394 else []) else (if i < 396 then (if i=395 then p395 else []) else (if i=396 then p396 else []))) else (if i < 402 then (if i < 401 then (if i=399 then p399 else []) else (if i=401 then p401 else [])) else (if i < 404 then (if i=402 then p402 else []) else (if i=404 then p404 else [])))) else (if i < 439 then (if i < 435 then (if i=414 then p414 else []) else (if i < 437 then (if i=435 then p435 else []) else (if i=437 then p437 else []))) else (if i < 444 then (if i < 441 then (if i=439 then p439 else []) else (if i=441 then p441 else [])) else (if i < 453 then (if i=444 then p444 else []) else (if i=453 then p453 else []))))) else (if i < 511 then (if i < 494 then (if i < 475 then (if i=474 then p474 else []) else (if i < 492 then (if i=475 then p475 else []) else (if i=492 then (if g then p492b else p492a) else []))) else (if i < 502 then (if i < 499 then (if i=494 then p494 else []) else (if i=499 then p499 else [])) else (if i < 504 then (if i=502 then p502 else []) else (if i=504 then p504 else [])))) else (if i < 514 then (if i < 512 then (if i=511 then p511 else []) else (if i < 513 then (if i=512 then (if g then p512b else p512a) else []) else (if i=513 then p513 else []))) else (if i < 521 then (if i < 520 then (if i=514 then p514 else []) else (if i=520 then p520 else [])) else (if i < 526 then (if i=521 then p521 else []) else (if i=526 then p526 else [])))))))) else (if i < 642 then (if i < 592 then (if i < 558 then (if i < 545 then (if i < 535 then (if i < 533 then (if i=528 then p528 else []) else (if i < 534 then (if i=533 then p533 else []) else (if i=534 then p534 else []))) else (if i < 540 then (if i=535 then p535 else []) else (if i < 544 then (if i=540 then p540 else []) else (if i=544 then p544 else [])))) else (if i < 551 then (if i < 546 then (if i=545 then p545 else []) else (if i < 550 then (if i=546 then p546 else []) else (if i=550 then p550 else []))) else (if i < 556 then (if i < 552 then (if i=551 then p551 else []) else (if i=552 then p552 else [])) else (if i < 557 then (if i=556 then p556 else []) else (if i=557 then p557 else []))))) else (if i < 581 then (if i < 565 then (if i < 560 then (if i=558 then p558 else []) else (if i < 564 then (if i=560 then (if g then p560b else p560a) else []) else (if i=564 then p564 else []))) else (if i < 569 then (if i < 568 then (if i=565 then (if g then p565b else p565a) else []) else (if i=568 then p568 else [])) else (if i < 580 then (if i=569 then p569 else []) else (if i=580 then p580 else [])))) else (if i < 587 then (if i < 585 then (if i=581 then p581 else []) else (if i < 586 then (if i=585 then p585 else []) else (if i=586 then p586 else []))) else (if i < 590 then (if i < 588 then (if i=587 then p587 else []) else (if i=588 then p588 else [])) else (if i < 591 then (if i=590 then p590 else []) else (if i=591 then p591 else [])))))) else (if i < 614 then (if i < 603 then (if i < 597 then (if i < 593 then (if i=592 then p592 else []) else (if i < 594 then (if i=593 then p593 else []) else (if i=594 then p594 else []))) else (if i < 601 then (if i < 598 then (if i=597 then p597 else []) else (if i=598 then p598 else [])) else (if i < 602 then (if i=601 then p601 else []) else (if i=602 then p602 else [])))) else (if i < 610 then (if i < 604 then (if i=603 then p603 else []) else (if i < 609 then (if i=604 then p604 else []) else (if i=609 then p609 else []))) else (if i < 612 then (if i < 611 then (if i=610 then p610 else []) else (if i=611 then p611 else [])) else (if i < 613 then (if i=612 then p612 else []) else (if i=613 then p613 else []))))) else (if i < 631 then (if i < 623 then (if i < 619 then (if i=614 then p614 else []) else (if i < 620 then (if i=619 then p619 else []) else (if i=620 then p620 else []))) else (if i < 625 then (if i < 624 then (if i=623 then p623 else []) else (if i=624 then p624 else [])) else (if i < 626 then (if i=625 then p625 else []) else (if i=626 then p626 else [])))) else (if i < 634 then (if i < 632 then (if i=631 then p631 else []) else (if i < 633 then (if i=632 then p632 else []) else (if i=633 then p633 else []))) else (if i < 636 then (if i < 635 then (if i=634 then p634 else []) else (if i=635 then p635 else [])) else (if i < 641 then (if i=636 then p636 else []) else (if i=641 then p641 else []))))))) else (if i < 704 then (if i < 677 then (if i < 654 then (if i < 647 then (if i < 645 then (if i=642 then p642 else []) else (if i < 646 then (if i=645 then p645 else []) else (if i=646 then p646 else []))) else (if i < 648 then (if i=647 then p647 else []) else (if i < 653 then (if i=648 then p648 else []) else (if i=653 then p653 else [])))) else (if i < 657 then (if i < 655 then (if i=654 then p654 else []) else (if i < 656 then (if i=655 then p655 else []) else (if i=656 then p656 else []))) else (if i < 673 then (if i < 658 then (if i=657 then p657 else []) else (if i=658 then p658 else [])) else (if i < 674 then (if i=673 then p673 else []) else (if i=674 then p674 else []))))) else (if i < 684 then (if i < 680 then (if i < 678 then (if i=677 then p677 else []) else (if i < 679 then (if i=678 then p678 else []) else (if i=679 then p679 else []))) else (if i < 682 then (if i < 681 then (if i=680 then p680 else []) else (if i=681 then p681 else [])) else (if i < 683 then (if i=682 then p682 else []) else (if i=683 then p683 else [])))) else (if i < 700 then (if i < 685 then (if i=684 then p684 else []) else (if i < 686 then (if i=685 then p685 else []) else (if i=686 then p686 else []))) else (if i < 702 then (if i < 701 then (if i=700 then p700 else []) else (if i=701 then p701 else [])) else (if i < 703 then (if i=702 then p702 else []) else (if i=703 then p703 else [])))))) else (if i < 718 then (if i < 711 then (if i < 707 then (if i < 705 then (if i=704 then p704 else []) else (if i < 706 then (if i=705 then p705 else []) else (if i=706 then p706 else []))) else (if i < 709 then (if i < 708 then (if i=707 then p707 else []) else (if i=708 then p708 else [])) else (if i < 710 then (if i=709 then p709 else []) else (if i=710 then p710 else [])))) else (if i < 714 then (if i < 712 then (if i=711 then p711 else []) else (if i < 713 then (if i=712 then p712 else []) else (if i=713 then p713 else []))) else (if i < 716 then (if i < 715 then (if i=714 then p714 else []) else (if i=715 then p715 else [])) else (if i < 717 then (if i=716 then p716 else []) else (if i=717 then p717 else []))))) else (if i < 725 then (if i < 721 then (if i < 719 then (if i=718 then p718 else []) else (if i < 720 then (if i=719 then p719 else []) else (if i=720 then p720 else []))) else (if i < 723 then (if i < 722 then (if i=721 then p721 else []) else (if i=722 then p722 else [])) else (if i < 724 then (if i=723 then p723 else []) else (if i=724 then p724 else [])))) else (if i < 728 then (if i < 726 then (if i=725 then p725 else []) else (if i < 727 then (if i=726 then p726 else []) else (if i=727 then p727 else []))) else (if i < 730 then (if i < 729 then (if i=728 then p728 else []) else (if i=729 then p729 else [])) else (if i < 731 then (if i=730 then p730 else []) else (if i=731 then p731 else [])))))))))

def live0 (i : Nat) := decide (1≤i ∧ i≤249)

def scalarK : Int := 80990493410131000784375977023646274345820490095244015289194989569855772668241364832628280392076492800000000000000

def sextic1 : Polynomial := [⟨(-83521:Int),[156,156]⟩,⟨(-9826:Int),[37,37,156]⟩,⟨(4913:Int),[156,156,156]⟩,⟨(867:Int),[37,37,37,37]⟩,⟨(578:Int),[37,37,156,156]⟩,⟨(-867:Int),[38,38,156,156]⟩,⟨(34:Int),[36,36,38,38,156]⟩,⟨(-51:Int),[37,37,37,37,156]⟩,⟨(1:Int),[36,36,36,36,38,38]⟩]

def poleF1 (g : Bool) (i : Nat) : Polynomial := if i=339 then sextic1 else original g i

def poleI1 := removeId 344 (removeId 341 parentIds)

def sextic2 : Polynomial := [⟨(-83521:Int),[171,171]⟩,⟨(-9826:Int),[41,41,171]⟩,⟨(4913:Int),[171,171,171]⟩,⟨(867:Int),[41,41,41,41]⟩,⟨(578:Int),[41,41,171,171]⟩,⟨(-867:Int),[42,42,171,171]⟩,⟨(34:Int),[40,40,42,42,171]⟩,⟨(-51:Int),[41,41,41,41,171]⟩,⟨(1:Int),[40,40,40,40,42,42]⟩]

def poleF2 (g : Bool) (i : Nat) : Polynomial := if i=389 then sextic2 else poleF1 g i

def poleI2 := removeId 394 (removeId 391 poleI1)

def sextic3 : Polynomial := [⟨(-83521:Int),[187,187]⟩,⟨(-9826:Int),[45,45,187]⟩,⟨(4913:Int),[187,187,187]⟩,⟨(867:Int),[45,45,45,45]⟩,⟨(578:Int),[45,45,187,187]⟩,⟨(-867:Int),[46,46,187,187]⟩,⟨(34:Int),[44,44,46,46,187]⟩,⟨(-51:Int),[45,45,45,45,187]⟩,⟨(1:Int),[44,44,44,44,46,46]⟩]

def poleF3 (g : Bool) (i : Nat) : Polynomial := if i=439 then sextic3 else poleF2 g i

def poleI3 := removeId 444 (removeId 441 poleI2)

def sextic4 : Polynomial := [⟨(-547852660565654646814043544513786333969991797007403046282478357320046759415057656674797877463818334938667360321881664798939886330042870968855554174788040470698566652765200203010639509273192858429046128640000000000000000000000000000:Int),[193,193]⟩,⟨(795812588247947213707278350234348291722032135675867694231629967513402822238139650845405483132543618252800000000000000:Int),[49,49,193]⟩,⟨(-2610050429133258157257955167195229646591439333900735515069328979730020550341186205597259074835328646338631150073324436282635043597139211730510445348095613501975975362104186609226856118039204881882654867165670017515632224042465822373697113033569709225343386948937174346197176724692828297015468622872576000000000000000000000000000000000000000000:Int),[193,193,193]⟩,⟨(867:Int),[49,49,49,49]⟩,⟨(3791367893187921431239055671375683972110669875483758105761095898408628092837769250344621989368985016876590728871153389612040735848047549957477883562546992876806689638513496214606501794278151269405163520000000000000000000000000000:Int),[49,49,193,193]⟩,⟨(-5687051839781882146858583507063525958166004813225637158641643847612942139256653875516932984053477525314886093306730084418061103772071324936216825343820489315210034457770244321909752691417226904107745280000000000000000000000000000:Int),[50,50,193,193]⟩,⟨(-2753676775944454026668783218803973327757896663238296519832629645375096270720206404309361533330600755200000000000000:Int),[48,48,50,50,193]⟩,⟨(4130515163916681040003174828205959991636844994857444779748944468062644406080309606464042299995901132800000000000000:Int),[49,49,49,49,193]⟩,⟨(1:Int),[48,48,48,48,50,50]⟩]

def poleF4 (g : Bool) (i : Nat) : Polynomial := if i=494 then sextic4 else poleF3 g i

def poleI4 := removeId 502 (removeId 499 poleI3)

def poleLive (i : Nat) := live0 i && ![35,39,43,47,157,172,188,194].contains i

def p514lateA : Polynomial := [⟨(129:Int),[6]⟩,⟨(-348:Int),[7]⟩]
def p514lateZ : Polynomial := [⟨(1661196939489159664631676359648545564879636658556837683994600390025912827028335705244979623638553602017173385255072446005969366136782922419129033885890782331090838366771778058187064222668265225741945760718824762759961838606798257615398044097867316538922203670174643952570360151838696:Int),[197]⟩,⟨(-1253733539237101633684284045017770237645008798910820893580830483038424775115725060562248772557398944918621422834016940381863672556062582957833233121427005532898745937186247591084576771825105830748638309976471519064122142344753401973885316300277220029375248052961995435902158605161280:Int),[198]⟩,⟨(28904300650622609951449334542726588945492315791119870748614623651940589077338126451890398845944258068366330917219814079816677573327738897653698863221945112925480240131366472050543123850825543706084515258038269801463821636671396297311969954022029951833820499596885227109101147798572088010846726063025730525454819822445870638421330673566095203912700451518425869833324939930827669709917198021945830699147056952789289030547336126312146337238540903479820385909497234920571995327996729295744286294857078649254503354278133866231059968721739094068292296562892116104903765487:Int),[6,6,197]⟩,⟨(-16516743228927205686542476881558050825995609023497068999208356372537479472764643686794513626253861753352189095554179474180958613330136512944970778983968635957417280075066555457453213629043167832048294433164725600836469506669369312749697116584017115333611714055362986919486370170612621720483843464586131728831325612826211793383617527752054402235828829439100497047614251389044382691381256012540474685226889687308165160312763500749797906993451944845611649091141277097469711615998131026139592168489759228145430488158933637846319982126708053753309883750224066345659294564:Int),[6,6,198]⟩,⟨(-33033486457854411373084953763116101651991218046994137998416712745074958945529287373589027252507723506704378191108358948361917226660273025889941557967937271914834560150133110914906427258086335664096588866329451201672939013338738625499394233168034230667223428110725973838972740341225243440967686929172263457662651225652423586767235055504108804471657658878200994095228502778088765382762512025080949370453779374616330320625527001499595813986903889691223298182282554194939423231996262052279184336979518456290860976317867275692639964253416107506619767500448132691318589128:Int),[6,7,197]⟩,⟨(115617202602490439805797338170906355781969263164479482994458494607762356309352505807561595383777032273465323668879256319266710293310955590614795452887780451701920960525465888202172495403302174824338061032153079205855286546685585189247879816088119807335281998387540908436404591194288352043386904252102922101819279289783482553685322694264380815650801806073703479333299759723310678839668792087783322796588227811157156122189344505248585348954163613919281543637988939682287981311986917182977145179428314597018013417112535464924239874886956376273169186251568464419615061948:Int),[6,7,198]⟩,⟨(57808601301245219902898669085453177890984631582239741497229247303881178154676252903780797691888516136732661834439628159633355146655477795307397726443890225850960480262732944101086247701651087412169030516076539602927643273342792594623939908044059903667640999193770454218202295597144176021693452126051461050909639644891741276842661347132190407825400903036851739666649879861655339419834396043891661398294113905578578061094672252624292674477081806959640771818994469841143990655993458591488572589714157298509006708556267732462119937443478188136584593125784232209807530974:Int),[7,7,197]⟩,⟨(-33033486457854411373084953763116101651991218046994137998416712745074958945529287373589027252507723506704378191108358948361917226660273025889941557967937271914834560150133110914906427258086335664096588866329451201672939013338738625499394233168034230667223428110725973838972740341225243440967686929172263457662651225652423586767235055504108804471657658878200994095228502778088765382762512025080949370453779374616330320625527001499595813986903889691223298182282554194939423231996262052279184336979518456290860976317867275692639964253416107506619767500448132691318589128:Int),[7,7,198]⟩]
def p514late : Polynomial := p514lateA ++ [⟨(-164:Int),[9]⟩] ++ p514lateZ


def numerator1 := scale (-1) (p346A ++ p346Z)

def stepF1 (g : Bool) (i : Nat) := substitute 159 (-1) numerator1 (poleF4 g i)

def stepI1 := removeId 346 poleI4

def live1 := dropSlot poleLive 159

def numerator2 := scale (-1) (p290A ++ p290Z)

def stepF2 (g : Bool) (i : Nat) := substitute 139 (-1) numerator2 (stepF1 g i)

def stepI2 := removeId 290 stepI1

def live2 := dropSlot live1 139

def numerator3 := scale (-1) (p298A ++ p298Z)

def stepF3 (g : Bool) (i : Nat) := substitute 145 (-1) numerator3 (stepF2 g i)

def stepI3 := removeId 298 stepI2

def live3 := dropSlot live2 145

def numerator4 := scale (-1) (p289A ++ p289Z)

def stepF4 (g : Bool) (i : Nat) := substitute 138 (-1) numerator4 (stepF3 g i)

def stepI4 := removeId 289 stepI3

def live4 := dropSlot live3 138

def numerator5 := scale (-1) (p363A ++ p363Z)

def stepF5 (g : Bool) (i : Nat) := substitute 168 (-1) numerator5 (stepF4 g i)

def stepI5 := removeId 363 stepI4

def live5 := dropSlot live4 168

def numerator6 := scale (-1) (p594A ++ p594Z)

def stepF6 (g : Bool) (i : Nat) := substitute 213 (1) numerator6 (stepF5 g i)

def stepI6 := removeId 594 stepI5

def live6 := dropSlot live5 213

def numerator7 := scale (-1) (p25A ++ p25Z)

def stepF7 (g : Bool) (i : Nat) := substitute 55 (-1) numerator7 (stepF6 g i)

def stepI7 := removeId 25 stepI6

def live7 := dropSlot live6 55

def numerator8 := scale (-1) (p593A ++ p593Z)

def stepF8 (g : Bool) (i : Nat) := substitute 212 (1) numerator8 (stepF7 g i)

def stepI8 := removeId 593 stepI7

def live8 := dropSlot live7 212

def numerator9 := scale (-1) (p396A ++ p396Z)

def stepF9 (g : Bool) (i : Nat) := substitute 174 (-1) numerator9 (stepF8 g i)

def stepI9 := removeId 396 stepI8

def live9 := dropSlot live8 174

def numerator10 := scale (-1) (p520A ++ p520Z)

def stepF10 (g : Bool) (i : Nat) := substitute 147 (-1) numerator10 (stepF9 g i)

def stepI10 := removeId 520 stepI9

def live10 := dropSlot live9 147

def numerator11 := scale (-1) (p24A ++ p24Z)

def stepF11 (g : Bool) (i : Nat) := substitute 54 (-1) numerator11 (stepF10 g i)

def stepI11 := removeId 24 stepI10

def live11 := dropSlot live10 54

def numerator12 := scale (-1) (p534A ++ p534Z)

def stepF12 (g : Bool) (i : Nat) := substitute 178 (-1) numerator12 (stepF11 g i)

def stepI12 := removeId 534 stepI11

def live12 := dropSlot live11 178

def numerator13 := scale (-1) (p513A ++ p513Z)

def stepF13 (g : Bool) (i : Nat) := substitute 8 (8) numerator13 (stepF12 g i)

def stepI13 := removeId 513 stepI12

def live13 := dropSlot live12 8

def numerator14 := scale (-1) (p401A ++ p401Z)

def stepF14 (g : Bool) (i : Nat) := substitute 176 (-4096) numerator14 (stepF13 g i)

def stepI14 := removeId 401 stepI13

def live14 := dropSlot live13 176

def numerator15 := scale (-1) (p514lateA ++ p514lateZ)

def stepF15 (g : Bool) (i : Nat) := substitute 9 (-164) numerator15 (stepF14 g i)

def stepI15 := removeId 514 stepI14

def live15 := dropSlot live14 9

def code (i : Nat) : Nat := i-(if 8 < i then 1 else 0) - (if 9 < i then 1 else 0) - (if 35 < i then 1 else 0) - (if 39 < i then 1 else 0) - (if 43 < i then 1 else 0) - (if 47 < i then 1 else 0) - (if 54 < i then 1 else 0) - (if 55 < i then 1 else 0) - (if 138 < i then 1 else 0) - (if 139 < i then 1 else 0) - (if 145 < i then 1 else 0) - (if 147 < i then 1 else 0) - (if 157 < i then 1 else 0) - (if 159 < i then 1 else 0) - (if 168 < i then 1 else 0) - (if 172 < i then 1 else 0) - (if 174 < i then 1 else 0) - (if 176 < i then 1 else 0) - (if 178 < i then 1 else 0) - (if 188 < i then 1 else 0) - (if 194 < i then 1 else 0) - (if 212 < i then 1 else 0) - (if 213 < i then 1 else 0)

def back (i : Nat) : Nat := i+(if 7 < i then 1 else 0) + (if 7 < i then 1 else 0) + (if 32 < i then 1 else 0) + (if 35 < i then 1 else 0) + (if 38 < i then 1 else 0) + (if 41 < i then 1 else 0) + (if 47 < i then 1 else 0) + (if 47 < i then 1 else 0) + (if 129 < i then 1 else 0) + (if 129 < i then 1 else 0) + (if 134 < i then 1 else 0) + (if 135 < i then 1 else 0) + (if 144 < i then 1 else 0) + (if 145 < i then 1 else 0) + (if 153 < i then 1 else 0) + (if 156 < i then 1 else 0) + (if 157 < i then 1 else 0) + (if 158 < i then 1 else 0) + (if 159 < i then 1 else 0) + (if 168 < i then 1 else 0) + (if 173 < i then 1 else 0) + (if 190 < i then 1 else 0) + (if 190 < i then 1 else 0)
end ProjectionDescent.Shared
