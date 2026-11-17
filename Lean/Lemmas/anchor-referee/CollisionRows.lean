import PhysicalAnchor
namespace AnchorCollision
open CircuitTransport StructuralReduction StructuralReduction.Transfer84
open ProjectionFibres.Comparison EllipticHeight.Labels AnchorCircuit
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192


private theorem e4 (x : Fin 84→Rat) : atWire x 4 = cell x 5 :=
  wireStep x (by decide) (show patch archiveAt 4=.var 5 from rfl) trivial

private theorem e5 (x : Fin 84→Rat) : atWire x 5 = cell x 6 :=
  wireStep x (by decide) (show patch archiveAt 5=.var 6 from rfl) trivial

private theorem e24 (x : Fin 84→Rat) : atWire x 24 = cell x 25 :=
  wireStep x (by decide) (show patch archiveAt 24=.var 25 from rfl) trivial

private theorem e25 (x : Fin 84→Rat) : atWire x 25 = cell x 26 :=
  wireStep x (by decide) (show patch archiveAt 25=.var 26 from rfl) trivial

private theorem e85 (x : Fin 84→Rat) : atWire x 85 = (2:Rat) :=
  wireStep x (by decide) (show patch archiveAt 85=.int (2) from rfl) trivial

private theorem e98 (x : Fin 84→Rat) : atWire x 98 = (-1:Rat) :=
  wireStep x (by decide) (show patch archiveAt 98=.int (-1) from rfl) trivial

private theorem e271 (x : Fin 84→Rat) : atWire x 271 = atWire x 256*atWire x 270 :=
  wireStep x (by decide) (show patch archiveAt 271=.mul 256 270 from rfl) ⟨by decide,by decide⟩

private theorem e289 (x : Fin 84→Rat) : atWire x 289 = atWire x 98*atWire x 288 :=
  wireStep x (by decide) (show patch archiveAt 289=.mul 98 288 from rfl) ⟨by decide,by decide⟩

private theorem e290 (x : Fin 84→Rat) : atWire x 290 = atWire x 282*atWire x 289 :=
  wireStep x (by decide) (show patch archiveAt 290=.mul 282 289 from rfl) ⟨by decide,by decide⟩

private theorem e291 (x : Fin 84→Rat) : atWire x 291 = atWire x 85*atWire x 290 :=
  wireStep x (by decide) (show patch archiveAt 291=.mul 85 290 from rfl) ⟨by decide,by decide⟩

private theorem e292 (x : Fin 84→Rat) : atWire x 292 = atWire x 271+atWire x 291 :=
  wireStep x (by decide) (show patch archiveAt 292=.add 271 291 from rfl) ⟨by decide,by decide⟩

private theorem e293 (x : Fin 84→Rat) : atWire x 293 = (256:Rat) :=
  wireStep x (by decide) (show patch archiveAt 293=.int (256) from rfl) trivial

private theorem e294 (x : Fin 84→Rat) : atWire x 294 = atWire x 292*atWire x 293 :=
  wireStep x (by decide) (show patch archiveAt 294=.mul 292 293 from rfl) ⟨by decide,by decide⟩

private theorem e301 (x : Fin 84→Rat) : atWire x 301 = (307328:Rat) :=
  wireStep x (by decide) (show patch archiveAt 301=.int (307328) from rfl) trivial

private theorem e464 (x : Fin 84→Rat) : atWire x 464 = (-3576:Rat) :=
  wireStep x (by decide) (show patch archiveAt 464=.int (-3576) from rfl) trivial

private theorem e465 (x : Fin 84→Rat) : atWire x 465 = (5521:Rat) :=
  wireStep x (by decide) (show patch archiveAt 465=.int (5521) from rfl) trivial

private theorem e466 (x : Fin 84→Rat) : atWire x 466 = (-7152:Rat) :=
  wireStep x (by decide) (show patch archiveAt 466=.int (-7152) from rfl) trivial

private theorem e467 (x : Fin 84→Rat) : atWire x 467 = (11042:Rat) :=
  wireStep x (by decide) (show patch archiveAt 467=.int (11042) from rfl) trivial

private theorem e517 (x : Fin 84→Rat) : atWire x 517 = atWire x 294*atWire x 516 :=
  wireStep x (by decide) (show patch archiveAt 517=.mul 294 516 from rfl) ⟨by decide,by decide⟩

private theorem e518 (x : Fin 84→Rat) : atWire x 518 = atWire x 4*atWire x 465 :=
  wireStep x (by decide) (show patch archiveAt 518=.mul 4 465 from rfl) ⟨by decide,by decide⟩

private theorem e519 (x : Fin 84→Rat) : atWire x 519 = atWire x 24*atWire x 518 :=
  wireStep x (by decide) (show patch archiveAt 519=.mul 24 518 from rfl) ⟨by decide,by decide⟩

private theorem e520 (x : Fin 84→Rat) : atWire x 520 = atWire x 4*atWire x 466 :=
  wireStep x (by decide) (show patch archiveAt 520=.mul 4 466 from rfl) ⟨by decide,by decide⟩

private theorem e521 (x : Fin 84→Rat) : atWire x 521 = atWire x 25*atWire x 520 :=
  wireStep x (by decide) (show patch archiveAt 521=.mul 25 520 from rfl) ⟨by decide,by decide⟩

private theorem e522 (x : Fin 84→Rat) : atWire x 522 = atWire x 519+atWire x 521 :=
  wireStep x (by decide) (show patch archiveAt 522=.add 519 521 from rfl) ⟨by decide,by decide⟩

private theorem e523 (x : Fin 84→Rat) : atWire x 523 = atWire x 5*atWire x 466 :=
  wireStep x (by decide) (show patch archiveAt 523=.mul 5 466 from rfl) ⟨by decide,by decide⟩

private theorem e524 (x : Fin 84→Rat) : atWire x 524 = atWire x 24*atWire x 523 :=
  wireStep x (by decide) (show patch archiveAt 524=.mul 24 523 from rfl) ⟨by decide,by decide⟩

private theorem e525 (x : Fin 84→Rat) : atWire x 525 = atWire x 522+atWire x 524 :=
  wireStep x (by decide) (show patch archiveAt 525=.add 522 524 from rfl) ⟨by decide,by decide⟩

private theorem e526 (x : Fin 84→Rat) : atWire x 526 = atWire x 5*atWire x 467 :=
  wireStep x (by decide) (show patch archiveAt 526=.mul 5 467 from rfl) ⟨by decide,by decide⟩

private theorem e527 (x : Fin 84→Rat) : atWire x 527 = atWire x 25*atWire x 526 :=
  wireStep x (by decide) (show patch archiveAt 527=.mul 25 526 from rfl) ⟨by decide,by decide⟩

private theorem e528 (x : Fin 84→Rat) : atWire x 528 = atWire x 525+atWire x 527 :=
  wireStep x (by decide) (show patch archiveAt 528=.add 525 527 from rfl) ⟨by decide,by decide⟩

private theorem e529 (x : Fin 84→Rat) : atWire x 529 = atWire x 301*atWire x 528 :=
  wireStep x (by decide) (show patch archiveAt 529=.mul 301 528 from rfl) ⟨by decide,by decide⟩

private theorem e530 (x : Fin 84→Rat) : atWire x 530 = atWire x 300*atWire x 529 :=
  wireStep x (by decide) (show patch archiveAt 530=.mul 300 529 from rfl) ⟨by decide,by decide⟩

private theorem e531 (x : Fin 84→Rat) : atWire x 531 = atWire x 517+atWire x 530 :=
  wireStep x (by decide) (show patch archiveAt 531=.add 517 530 from rfl) ⟨by decide,by decide⟩

private theorem e534 (x : Fin 84→Rat) : atWire x 534 = atWire x 305*atWire x 533 :=
  wireStep x (by decide) (show patch archiveAt 534=.mul 305 533 from rfl) ⟨by decide,by decide⟩

private theorem e535 (x : Fin 84→Rat) : atWire x 535 = atWire x 531+atWire x 534 :=
  wireStep x (by decide) (show patch archiveAt 535=.add 531 534 from rfl) ⟨by decide,by decide⟩

private theorem e537 (x : Fin 84→Rat) : atWire x 537 = atWire x 294*atWire x 536 :=
  wireStep x (by decide) (show patch archiveAt 537=.mul 294 536 from rfl) ⟨by decide,by decide⟩

private theorem e538 (x : Fin 84→Rat) : atWire x 538 = atWire x 535+atWire x 537 :=
  wireStep x (by decide) (show patch archiveAt 538=.add 535 537 from rfl) ⟨by decide,by decide⟩

private theorem e541 (x : Fin 84→Rat) : atWire x 541 = atWire x 305*atWire x 540 :=
  wireStep x (by decide) (show patch archiveAt 541=.mul 305 540 from rfl) ⟨by decide,by decide⟩

private theorem e542 (x : Fin 84→Rat) : atWire x 542 = atWire x 538+atWire x 541 :=
  wireStep x (by decide) (show patch archiveAt 542=.add 538 541 from rfl) ⟨by decide,by decide⟩

private theorem e545 (x : Fin 84→Rat) : atWire x 545 = atWire x 294*atWire x 544 :=
  wireStep x (by decide) (show patch archiveAt 545=.mul 294 544 from rfl) ⟨by decide,by decide⟩

private theorem e546 (x : Fin 84→Rat) : atWire x 546 = atWire x 542+atWire x 545 :=
  wireStep x (by decide) (show patch archiveAt 546=.add 542 545 from rfl) ⟨by decide,by decide⟩

private theorem e549 (x : Fin 84→Rat) : atWire x 549 = atWire x 305*atWire x 548 :=
  wireStep x (by decide) (show patch archiveAt 549=.mul 305 548 from rfl) ⟨by decide,by decide⟩

private theorem e550 (x : Fin 84→Rat) : atWire x 550 = atWire x 546+atWire x 549 :=
  wireStep x (by decide) (show patch archiveAt 550=.add 546 549 from rfl) ⟨by decide,by decide⟩

private theorem e552 (x : Fin 84→Rat) : atWire x 552 = atWire x 294*atWire x 551 :=
  wireStep x (by decide) (show patch archiveAt 552=.mul 294 551 from rfl) ⟨by decide,by decide⟩

private theorem e553 (x : Fin 84→Rat) : atWire x 553 = atWire x 550+atWire x 552 :=
  wireStep x (by decide) (show patch archiveAt 553=.add 550 552 from rfl) ⟨by decide,by decide⟩

private theorem e556 (x : Fin 84→Rat) : atWire x 556 = atWire x 305*atWire x 555 :=
  wireStep x (by decide) (show patch archiveAt 556=.mul 305 555 from rfl) ⟨by decide,by decide⟩

private theorem e557 (x : Fin 84→Rat) : atWire x 557 = atWire x 553+atWire x 556 :=
  wireStep x (by decide) (show patch archiveAt 557=.add 553 556 from rfl) ⟨by decide,by decide⟩

private theorem e562 (x : Fin 84→Rat) : atWire x 562 = atWire x 294*atWire x 561 :=
  wireStep x (by decide) (show patch archiveAt 562=.mul 294 561 from rfl) ⟨by decide,by decide⟩

private theorem e563 (x : Fin 84→Rat) : atWire x 563 = atWire x 557+atWire x 562 :=
  wireStep x (by decide) (show patch archiveAt 563=.add 557 562 from rfl) ⟨by decide,by decide⟩

private theorem e568 (x : Fin 84→Rat) : atWire x 568 = atWire x 305*atWire x 567 :=
  wireStep x (by decide) (show patch archiveAt 568=.mul 305 567 from rfl) ⟨by decide,by decide⟩

private theorem e569 (x : Fin 84→Rat) : atWire x 569 = atWire x 563+atWire x 568 :=
  wireStep x (by decide) (show patch archiveAt 569=.add 563 568 from rfl) ⟨by decide,by decide⟩

private theorem e571 (x : Fin 84→Rat) : atWire x 571 = atWire x 294*atWire x 570 :=
  wireStep x (by decide) (show patch archiveAt 571=.mul 294 570 from rfl) ⟨by decide,by decide⟩

private theorem e572 (x : Fin 84→Rat) : atWire x 572 = atWire x 569+atWire x 571 :=
  wireStep x (by decide) (show patch archiveAt 572=.add 569 571 from rfl) ⟨by decide,by decide⟩

private theorem e577 (x : Fin 84→Rat) : atWire x 577 = atWire x 305*atWire x 576 :=
  wireStep x (by decide) (show patch archiveAt 577=.mul 305 576 from rfl) ⟨by decide,by decide⟩

private theorem e578 (x : Fin 84→Rat) : atWire x 578 = atWire x 572+atWire x 577 :=
  wireStep x (by decide) (show patch archiveAt 578=.add 572 577 from rfl) ⟨by decide,by decide⟩

private theorem e583 (x : Fin 84→Rat) : atWire x 583 = atWire x 294*atWire x 582 :=
  wireStep x (by decide) (show patch archiveAt 583=.mul 294 582 from rfl) ⟨by decide,by decide⟩

private theorem e584 (x : Fin 84→Rat) : atWire x 584 = atWire x 578+atWire x 583 :=
  wireStep x (by decide) (show patch archiveAt 584=.add 578 583 from rfl) ⟨by decide,by decide⟩

private theorem e589 (x : Fin 84→Rat) : atWire x 589 = atWire x 305*atWire x 588 :=
  wireStep x (by decide) (show patch archiveAt 589=.mul 305 588 from rfl) ⟨by decide,by decide⟩

private theorem e590 (x : Fin 84→Rat) : atWire x 590 = atWire x 584+atWire x 589 :=
  wireStep x (by decide) (show patch archiveAt 590=.add 584 589 from rfl) ⟨by decide,by decide⟩

private theorem e592 (x : Fin 84→Rat) : atWire x 592 = atWire x 294*atWire x 591 :=
  wireStep x (by decide) (show patch archiveAt 592=.mul 294 591 from rfl) ⟨by decide,by decide⟩

private theorem e593 (x : Fin 84→Rat) : atWire x 593 = atWire x 590+atWire x 592 :=
  wireStep x (by decide) (show patch archiveAt 593=.add 590 592 from rfl) ⟨by decide,by decide⟩

private theorem e598 (x : Fin 84→Rat) : atWire x 598 = atWire x 305*atWire x 597 :=
  wireStep x (by decide) (show patch archiveAt 598=.mul 305 597 from rfl) ⟨by decide,by decide⟩

private theorem e599 (x : Fin 84→Rat) : atWire x 599 = atWire x 593+atWire x 598 :=
  wireStep x (by decide) (show patch archiveAt 599=.add 593 598 from rfl) ⟨by decide,by decide⟩

private theorem e604 (x : Fin 84→Rat) : atWire x 604 = atWire x 294*atWire x 603 :=
  wireStep x (by decide) (show patch archiveAt 604=.mul 294 603 from rfl) ⟨by decide,by decide⟩

private theorem e605 (x : Fin 84→Rat) : atWire x 605 = atWire x 599+atWire x 604 :=
  wireStep x (by decide) (show patch archiveAt 605=.add 599 604 from rfl) ⟨by decide,by decide⟩

private theorem e610 (x : Fin 84→Rat) : atWire x 610 = atWire x 305*atWire x 609 :=
  wireStep x (by decide) (show patch archiveAt 610=.mul 305 609 from rfl) ⟨by decide,by decide⟩

private theorem e611 (x : Fin 84→Rat) : atWire x 611 = atWire x 605+atWire x 610 :=
  wireStep x (by decide) (show patch archiveAt 611=.add 605 610 from rfl) ⟨by decide,by decide⟩

private theorem e613 (x : Fin 84→Rat) : atWire x 613 = atWire x 294*atWire x 612 :=
  wireStep x (by decide) (show patch archiveAt 613=.mul 294 612 from rfl) ⟨by decide,by decide⟩

private theorem e614 (x : Fin 84→Rat) : atWire x 614 = atWire x 611+atWire x 613 :=
  wireStep x (by decide) (show patch archiveAt 614=.add 611 613 from rfl) ⟨by decide,by decide⟩

private theorem e619 (x : Fin 84→Rat) : atWire x 619 = atWire x 305*atWire x 618 :=
  wireStep x (by decide) (show patch archiveAt 619=.mul 305 618 from rfl) ⟨by decide,by decide⟩

private theorem e620 (x : Fin 84→Rat) : atWire x 620 = atWire x 614+atWire x 619 :=
  wireStep x (by decide) (show patch archiveAt 620=.add 614 619 from rfl) ⟨by decide,by decide⟩

private theorem e625 (x : Fin 84→Rat) : atWire x 625 = atWire x 294*atWire x 624 :=
  wireStep x (by decide) (show patch archiveAt 625=.mul 294 624 from rfl) ⟨by decide,by decide⟩

private theorem e626 (x : Fin 84→Rat) : atWire x 626 = atWire x 620+atWire x 625 :=
  wireStep x (by decide) (show patch archiveAt 626=.add 620 625 from rfl) ⟨by decide,by decide⟩

private theorem e631 (x : Fin 84→Rat) : atWire x 631 = atWire x 305*atWire x 630 :=
  wireStep x (by decide) (show patch archiveAt 631=.mul 305 630 from rfl) ⟨by decide,by decide⟩

private theorem e632 (x : Fin 84→Rat) : atWire x 632 = atWire x 626+atWire x 631 :=
  wireStep x (by decide) (show patch archiveAt 632=.add 626 631 from rfl) ⟨by decide,by decide⟩

private theorem e634 (x : Fin 84→Rat) : atWire x 634 = atWire x 294*atWire x 633 :=
  wireStep x (by decide) (show patch archiveAt 634=.mul 294 633 from rfl) ⟨by decide,by decide⟩

private theorem e635 (x : Fin 84→Rat) : atWire x 635 = atWire x 632+atWire x 634 :=
  wireStep x (by decide) (show patch archiveAt 635=.add 632 634 from rfl) ⟨by decide,by decide⟩

private theorem e640 (x : Fin 84→Rat) : atWire x 640 = atWire x 305*atWire x 639 :=
  wireStep x (by decide) (show patch archiveAt 640=.mul 305 639 from rfl) ⟨by decide,by decide⟩

private theorem e641 (x : Fin 84→Rat) : atWire x 641 = atWire x 635+atWire x 640 :=
  wireStep x (by decide) (show patch archiveAt 641=.add 635 640 from rfl) ⟨by decide,by decide⟩

private theorem e645 (x : Fin 84→Rat) : atWire x 645 = atWire x 294*atWire x 644 :=
  wireStep x (by decide) (show patch archiveAt 645=.mul 294 644 from rfl) ⟨by decide,by decide⟩

private theorem e646 (x : Fin 84→Rat) : atWire x 646 = atWire x 641+atWire x 645 :=
  wireStep x (by decide) (show patch archiveAt 646=.add 641 645 from rfl) ⟨by decide,by decide⟩

private theorem e650 (x : Fin 84→Rat) : atWire x 650 = atWire x 305*atWire x 649 :=
  wireStep x (by decide) (show patch archiveAt 650=.mul 305 649 from rfl) ⟨by decide,by decide⟩

private theorem e651 (x : Fin 84→Rat) : atWire x 651 = atWire x 646+atWire x 650 :=
  wireStep x (by decide) (show patch archiveAt 651=.add 646 650 from rfl) ⟨by decide,by decide⟩

private theorem e653 (x : Fin 84→Rat) : atWire x 653 = atWire x 294*atWire x 652 :=
  wireStep x (by decide) (show patch archiveAt 653=.mul 294 652 from rfl) ⟨by decide,by decide⟩

private theorem e654 (x : Fin 84→Rat) : atWire x 654 = atWire x 651+atWire x 653 :=
  wireStep x (by decide) (show patch archiveAt 654=.add 651 653 from rfl) ⟨by decide,by decide⟩

private theorem e658 (x : Fin 84→Rat) : atWire x 658 = atWire x 305*atWire x 657 :=
  wireStep x (by decide) (show patch archiveAt 658=.mul 305 657 from rfl) ⟨by decide,by decide⟩

private theorem e659 (x : Fin 84→Rat) : atWire x 659 = atWire x 654+atWire x 658 :=
  wireStep x (by decide) (show patch archiveAt 659=.add 654 658 from rfl) ⟨by decide,by decide⟩

private theorem e663 (x : Fin 84→Rat) : atWire x 663 = atWire x 294*atWire x 662 :=
  wireStep x (by decide) (show patch archiveAt 663=.mul 294 662 from rfl) ⟨by decide,by decide⟩

private theorem e664 (x : Fin 84→Rat) : atWire x 664 = atWire x 659+atWire x 663 :=
  wireStep x (by decide) (show patch archiveAt 664=.add 659 663 from rfl) ⟨by decide,by decide⟩

private theorem e668 (x : Fin 84→Rat) : atWire x 668 = atWire x 305*atWire x 667 :=
  wireStep x (by decide) (show patch archiveAt 668=.mul 305 667 from rfl) ⟨by decide,by decide⟩

private theorem e669 (x : Fin 84→Rat) : atWire x 669 = atWire x 664+atWire x 668 :=
  wireStep x (by decide) (show patch archiveAt 669=.add 664 668 from rfl) ⟨by decide,by decide⟩

private theorem e671 (x : Fin 84→Rat) : atWire x 671 = atWire x 294*atWire x 670 :=
  wireStep x (by decide) (show patch archiveAt 671=.mul 294 670 from rfl) ⟨by decide,by decide⟩

private theorem e672 (x : Fin 84→Rat) : atWire x 672 = atWire x 669+atWire x 671 :=
  wireStep x (by decide) (show patch archiveAt 672=.add 669 671 from rfl) ⟨by decide,by decide⟩

private theorem e676 (x : Fin 84→Rat) : atWire x 676 = atWire x 305*atWire x 675 :=
  wireStep x (by decide) (show patch archiveAt 676=.mul 305 675 from rfl) ⟨by decide,by decide⟩

private theorem e677 (x : Fin 84→Rat) : atWire x 677 = atWire x 672+atWire x 676 :=
  wireStep x (by decide) (show patch archiveAt 677=.add 672 676 from rfl) ⟨by decide,by decide⟩

private theorem e680 (x : Fin 84→Rat) : atWire x 680 = atWire x 294*atWire x 679 :=
  wireStep x (by decide) (show patch archiveAt 680=.mul 294 679 from rfl) ⟨by decide,by decide⟩

private theorem e681 (x : Fin 84→Rat) : atWire x 681 = atWire x 4*atWire x 464 :=
  wireStep x (by decide) (show patch archiveAt 681=.mul 4 464 from rfl) ⟨by decide,by decide⟩

private theorem e682 (x : Fin 84→Rat) : atWire x 682 = atWire x 24*atWire x 681 :=
  wireStep x (by decide) (show patch archiveAt 682=.mul 24 681 from rfl) ⟨by decide,by decide⟩

private theorem e683 (x : Fin 84→Rat) : atWire x 683 = atWire x 25*atWire x 518 :=
  wireStep x (by decide) (show patch archiveAt 683=.mul 25 518 from rfl) ⟨by decide,by decide⟩

private theorem e684 (x : Fin 84→Rat) : atWire x 684 = atWire x 682+atWire x 683 :=
  wireStep x (by decide) (show patch archiveAt 684=.add 682 683 from rfl) ⟨by decide,by decide⟩

private theorem e685 (x : Fin 84→Rat) : atWire x 685 = atWire x 5*atWire x 465 :=
  wireStep x (by decide) (show patch archiveAt 685=.mul 5 465 from rfl) ⟨by decide,by decide⟩

private theorem e686 (x : Fin 84→Rat) : atWire x 686 = atWire x 24*atWire x 685 :=
  wireStep x (by decide) (show patch archiveAt 686=.mul 24 685 from rfl) ⟨by decide,by decide⟩

private theorem e687 (x : Fin 84→Rat) : atWire x 687 = atWire x 684+atWire x 686 :=
  wireStep x (by decide) (show patch archiveAt 687=.add 684 686 from rfl) ⟨by decide,by decide⟩

private theorem e688 (x : Fin 84→Rat) : atWire x 688 = atWire x 25*atWire x 523 :=
  wireStep x (by decide) (show patch archiveAt 688=.mul 25 523 from rfl) ⟨by decide,by decide⟩

private theorem e689 (x : Fin 84→Rat) : atWire x 689 = atWire x 687+atWire x 688 :=
  wireStep x (by decide) (show patch archiveAt 689=.add 687 688 from rfl) ⟨by decide,by decide⟩

private theorem e690 (x : Fin 84→Rat) : atWire x 690 = atWire x 301*atWire x 689 :=
  wireStep x (by decide) (show patch archiveAt 690=.mul 301 689 from rfl) ⟨by decide,by decide⟩

private theorem e691 (x : Fin 84→Rat) : atWire x 691 = atWire x 300*atWire x 690 :=
  wireStep x (by decide) (show patch archiveAt 691=.mul 300 690 from rfl) ⟨by decide,by decide⟩

private theorem e692 (x : Fin 84→Rat) : atWire x 692 = atWire x 680+atWire x 691 :=
  wireStep x (by decide) (show patch archiveAt 692=.add 680 691 from rfl) ⟨by decide,by decide⟩

private theorem e693 (x : Fin 84→Rat) : atWire x 693 = atWire x 305*atWire x 516 :=
  wireStep x (by decide) (show patch archiveAt 693=.mul 305 516 from rfl) ⟨by decide,by decide⟩

private theorem e694 (x : Fin 84→Rat) : atWire x 694 = atWire x 692+atWire x 693 :=
  wireStep x (by decide) (show patch archiveAt 694=.add 692 693 from rfl) ⟨by decide,by decide⟩

private theorem e696 (x : Fin 84→Rat) : atWire x 696 = atWire x 294*atWire x 695 :=
  wireStep x (by decide) (show patch archiveAt 696=.mul 294 695 from rfl) ⟨by decide,by decide⟩

private theorem e697 (x : Fin 84→Rat) : atWire x 697 = atWire x 694+atWire x 696 :=
  wireStep x (by decide) (show patch archiveAt 697=.add 694 696 from rfl) ⟨by decide,by decide⟩

private theorem e698 (x : Fin 84→Rat) : atWire x 698 = atWire x 305*atWire x 536 :=
  wireStep x (by decide) (show patch archiveAt 698=.mul 305 536 from rfl) ⟨by decide,by decide⟩

private theorem e699 (x : Fin 84→Rat) : atWire x 699 = atWire x 697+atWire x 698 :=
  wireStep x (by decide) (show patch archiveAt 699=.add 697 698 from rfl) ⟨by decide,by decide⟩

private theorem e702 (x : Fin 84→Rat) : atWire x 702 = atWire x 294*atWire x 701 :=
  wireStep x (by decide) (show patch archiveAt 702=.mul 294 701 from rfl) ⟨by decide,by decide⟩

private theorem e703 (x : Fin 84→Rat) : atWire x 703 = atWire x 699+atWire x 702 :=
  wireStep x (by decide) (show patch archiveAt 703=.add 699 702 from rfl) ⟨by decide,by decide⟩

private theorem e704 (x : Fin 84→Rat) : atWire x 704 = atWire x 305*atWire x 544 :=
  wireStep x (by decide) (show patch archiveAt 704=.mul 305 544 from rfl) ⟨by decide,by decide⟩

private theorem e705 (x : Fin 84→Rat) : atWire x 705 = atWire x 703+atWire x 704 :=
  wireStep x (by decide) (show patch archiveAt 705=.add 703 704 from rfl) ⟨by decide,by decide⟩

private theorem e707 (x : Fin 84→Rat) : atWire x 707 = atWire x 294*atWire x 706 :=
  wireStep x (by decide) (show patch archiveAt 707=.mul 294 706 from rfl) ⟨by decide,by decide⟩

private theorem e708 (x : Fin 84→Rat) : atWire x 708 = atWire x 705+atWire x 707 :=
  wireStep x (by decide) (show patch archiveAt 708=.add 705 707 from rfl) ⟨by decide,by decide⟩

private theorem e709 (x : Fin 84→Rat) : atWire x 709 = atWire x 305*atWire x 551 :=
  wireStep x (by decide) (show patch archiveAt 709=.mul 305 551 from rfl) ⟨by decide,by decide⟩

private theorem e710 (x : Fin 84→Rat) : atWire x 710 = atWire x 708+atWire x 709 :=
  wireStep x (by decide) (show patch archiveAt 710=.add 708 709 from rfl) ⟨by decide,by decide⟩

private theorem e715 (x : Fin 84→Rat) : atWire x 715 = atWire x 294*atWire x 714 :=
  wireStep x (by decide) (show patch archiveAt 715=.mul 294 714 from rfl) ⟨by decide,by decide⟩

private theorem e716 (x : Fin 84→Rat) : atWire x 716 = atWire x 710+atWire x 715 :=
  wireStep x (by decide) (show patch archiveAt 716=.add 710 715 from rfl) ⟨by decide,by decide⟩

private theorem e717 (x : Fin 84→Rat) : atWire x 717 = atWire x 305*atWire x 561 :=
  wireStep x (by decide) (show patch archiveAt 717=.mul 305 561 from rfl) ⟨by decide,by decide⟩

private theorem e718 (x : Fin 84→Rat) : atWire x 718 = atWire x 716+atWire x 717 :=
  wireStep x (by decide) (show patch archiveAt 718=.add 716 717 from rfl) ⟨by decide,by decide⟩

private theorem e720 (x : Fin 84→Rat) : atWire x 720 = atWire x 294*atWire x 719 :=
  wireStep x (by decide) (show patch archiveAt 720=.mul 294 719 from rfl) ⟨by decide,by decide⟩

private theorem e721 (x : Fin 84→Rat) : atWire x 721 = atWire x 718+atWire x 720 :=
  wireStep x (by decide) (show patch archiveAt 721=.add 718 720 from rfl) ⟨by decide,by decide⟩

private theorem e722 (x : Fin 84→Rat) : atWire x 722 = atWire x 305*atWire x 570 :=
  wireStep x (by decide) (show patch archiveAt 722=.mul 305 570 from rfl) ⟨by decide,by decide⟩

private theorem e723 (x : Fin 84→Rat) : atWire x 723 = atWire x 721+atWire x 722 :=
  wireStep x (by decide) (show patch archiveAt 723=.add 721 722 from rfl) ⟨by decide,by decide⟩

private theorem e728 (x : Fin 84→Rat) : atWire x 728 = atWire x 294*atWire x 727 :=
  wireStep x (by decide) (show patch archiveAt 728=.mul 294 727 from rfl) ⟨by decide,by decide⟩

private theorem e729 (x : Fin 84→Rat) : atWire x 729 = atWire x 723+atWire x 728 :=
  wireStep x (by decide) (show patch archiveAt 729=.add 723 728 from rfl) ⟨by decide,by decide⟩

private theorem e730 (x : Fin 84→Rat) : atWire x 730 = atWire x 305*atWire x 582 :=
  wireStep x (by decide) (show patch archiveAt 730=.mul 305 582 from rfl) ⟨by decide,by decide⟩

private theorem e731 (x : Fin 84→Rat) : atWire x 731 = atWire x 729+atWire x 730 :=
  wireStep x (by decide) (show patch archiveAt 731=.add 729 730 from rfl) ⟨by decide,by decide⟩

private theorem e733 (x : Fin 84→Rat) : atWire x 733 = atWire x 294*atWire x 732 :=
  wireStep x (by decide) (show patch archiveAt 733=.mul 294 732 from rfl) ⟨by decide,by decide⟩

private theorem e734 (x : Fin 84→Rat) : atWire x 734 = atWire x 731+atWire x 733 :=
  wireStep x (by decide) (show patch archiveAt 734=.add 731 733 from rfl) ⟨by decide,by decide⟩

private theorem e735 (x : Fin 84→Rat) : atWire x 735 = atWire x 305*atWire x 591 :=
  wireStep x (by decide) (show patch archiveAt 735=.mul 305 591 from rfl) ⟨by decide,by decide⟩

private theorem e736 (x : Fin 84→Rat) : atWire x 736 = atWire x 734+atWire x 735 :=
  wireStep x (by decide) (show patch archiveAt 736=.add 734 735 from rfl) ⟨by decide,by decide⟩

private theorem e739 (x : Fin 84→Rat) : atWire x 739 = atWire x 294*atWire x 738 :=
  wireStep x (by decide) (show patch archiveAt 739=.mul 294 738 from rfl) ⟨by decide,by decide⟩

private theorem e740 (x : Fin 84→Rat) : atWire x 740 = atWire x 736+atWire x 739 :=
  wireStep x (by decide) (show patch archiveAt 740=.add 736 739 from rfl) ⟨by decide,by decide⟩

private theorem e741 (x : Fin 84→Rat) : atWire x 741 = atWire x 305*atWire x 603 :=
  wireStep x (by decide) (show patch archiveAt 741=.mul 305 603 from rfl) ⟨by decide,by decide⟩

private theorem e742 (x : Fin 84→Rat) : atWire x 742 = atWire x 740+atWire x 741 :=
  wireStep x (by decide) (show patch archiveAt 742=.add 740 741 from rfl) ⟨by decide,by decide⟩

private theorem e744 (x : Fin 84→Rat) : atWire x 744 = atWire x 294*atWire x 743 :=
  wireStep x (by decide) (show patch archiveAt 744=.mul 294 743 from rfl) ⟨by decide,by decide⟩

private theorem e745 (x : Fin 84→Rat) : atWire x 745 = atWire x 742+atWire x 744 :=
  wireStep x (by decide) (show patch archiveAt 745=.add 742 744 from rfl) ⟨by decide,by decide⟩

private theorem e746 (x : Fin 84→Rat) : atWire x 746 = atWire x 305*atWire x 612 :=
  wireStep x (by decide) (show patch archiveAt 746=.mul 305 612 from rfl) ⟨by decide,by decide⟩

private theorem e747 (x : Fin 84→Rat) : atWire x 747 = atWire x 745+atWire x 746 :=
  wireStep x (by decide) (show patch archiveAt 747=.add 745 746 from rfl) ⟨by decide,by decide⟩

private theorem e750 (x : Fin 84→Rat) : atWire x 750 = atWire x 294*atWire x 749 :=
  wireStep x (by decide) (show patch archiveAt 750=.mul 294 749 from rfl) ⟨by decide,by decide⟩

private theorem e751 (x : Fin 84→Rat) : atWire x 751 = atWire x 747+atWire x 750 :=
  wireStep x (by decide) (show patch archiveAt 751=.add 747 750 from rfl) ⟨by decide,by decide⟩

private theorem e752 (x : Fin 84→Rat) : atWire x 752 = atWire x 305*atWire x 624 :=
  wireStep x (by decide) (show patch archiveAt 752=.mul 305 624 from rfl) ⟨by decide,by decide⟩

private theorem e753 (x : Fin 84→Rat) : atWire x 753 = atWire x 751+atWire x 752 :=
  wireStep x (by decide) (show patch archiveAt 753=.add 751 752 from rfl) ⟨by decide,by decide⟩

private theorem e755 (x : Fin 84→Rat) : atWire x 755 = atWire x 294*atWire x 754 :=
  wireStep x (by decide) (show patch archiveAt 755=.mul 294 754 from rfl) ⟨by decide,by decide⟩

private theorem e756 (x : Fin 84→Rat) : atWire x 756 = atWire x 753+atWire x 755 :=
  wireStep x (by decide) (show patch archiveAt 756=.add 753 755 from rfl) ⟨by decide,by decide⟩

private theorem e757 (x : Fin 84→Rat) : atWire x 757 = atWire x 305*atWire x 633 :=
  wireStep x (by decide) (show patch archiveAt 757=.mul 305 633 from rfl) ⟨by decide,by decide⟩

private theorem e758 (x : Fin 84→Rat) : atWire x 758 = atWire x 756+atWire x 757 :=
  wireStep x (by decide) (show patch archiveAt 758=.add 756 757 from rfl) ⟨by decide,by decide⟩

private theorem e762 (x : Fin 84→Rat) : atWire x 762 = atWire x 294*atWire x 761 :=
  wireStep x (by decide) (show patch archiveAt 762=.mul 294 761 from rfl) ⟨by decide,by decide⟩

private theorem e763 (x : Fin 84→Rat) : atWire x 763 = atWire x 758+atWire x 762 :=
  wireStep x (by decide) (show patch archiveAt 763=.add 758 762 from rfl) ⟨by decide,by decide⟩

private theorem e764 (x : Fin 84→Rat) : atWire x 764 = atWire x 305*atWire x 644 :=
  wireStep x (by decide) (show patch archiveAt 764=.mul 305 644 from rfl) ⟨by decide,by decide⟩

private theorem e765 (x : Fin 84→Rat) : atWire x 765 = atWire x 763+atWire x 764 :=
  wireStep x (by decide) (show patch archiveAt 765=.add 763 764 from rfl) ⟨by decide,by decide⟩

private theorem e767 (x : Fin 84→Rat) : atWire x 767 = atWire x 294*atWire x 766 :=
  wireStep x (by decide) (show patch archiveAt 767=.mul 294 766 from rfl) ⟨by decide,by decide⟩

private theorem e768 (x : Fin 84→Rat) : atWire x 768 = atWire x 765+atWire x 767 :=
  wireStep x (by decide) (show patch archiveAt 768=.add 765 767 from rfl) ⟨by decide,by decide⟩

private theorem e769 (x : Fin 84→Rat) : atWire x 769 = atWire x 305*atWire x 652 :=
  wireStep x (by decide) (show patch archiveAt 769=.mul 305 652 from rfl) ⟨by decide,by decide⟩

private theorem e770 (x : Fin 84→Rat) : atWire x 770 = atWire x 768+atWire x 769 :=
  wireStep x (by decide) (show patch archiveAt 770=.add 768 769 from rfl) ⟨by decide,by decide⟩

private theorem e774 (x : Fin 84→Rat) : atWire x 774 = atWire x 294*atWire x 773 :=
  wireStep x (by decide) (show patch archiveAt 774=.mul 294 773 from rfl) ⟨by decide,by decide⟩

private theorem e775 (x : Fin 84→Rat) : atWire x 775 = atWire x 770+atWire x 774 :=
  wireStep x (by decide) (show patch archiveAt 775=.add 770 774 from rfl) ⟨by decide,by decide⟩

private theorem e776 (x : Fin 84→Rat) : atWire x 776 = atWire x 305*atWire x 662 :=
  wireStep x (by decide) (show patch archiveAt 776=.mul 305 662 from rfl) ⟨by decide,by decide⟩

private theorem e777 (x : Fin 84→Rat) : atWire x 777 = atWire x 775+atWire x 776 :=
  wireStep x (by decide) (show patch archiveAt 777=.add 775 776 from rfl) ⟨by decide,by decide⟩

private theorem e779 (x : Fin 84→Rat) : atWire x 779 = atWire x 294*atWire x 778 :=
  wireStep x (by decide) (show patch archiveAt 779=.mul 294 778 from rfl) ⟨by decide,by decide⟩

private theorem e780 (x : Fin 84→Rat) : atWire x 780 = atWire x 777+atWire x 779 :=
  wireStep x (by decide) (show patch archiveAt 780=.add 777 779 from rfl) ⟨by decide,by decide⟩

private theorem e781 (x : Fin 84→Rat) : atWire x 781 = atWire x 305*atWire x 670 :=
  wireStep x (by decide) (show patch archiveAt 781=.mul 305 670 from rfl) ⟨by decide,by decide⟩

private theorem e782 (x : Fin 84→Rat) : atWire x 782 = atWire x 780+atWire x 781 :=
  wireStep x (by decide) (show patch archiveAt 782=.add 780 781 from rfl) ⟨by decide,by decide⟩

theorem zeroReciprocals (x : Fin 84→Rat)
    (zero : numerator (rootH x 1) (rootJ x 1)=(0,0)) : atWire x 294=0 ∧ atWire x 305=0 := by
  constructor
  · simp only [e294,e293,e292,e291,e290,e289,e271,e98,e85,numerator_1,numerator_2,zero,Rat.mul_zero,Rat.zero_mul,Rat.zero_add]
  · rw [quotient_wire,zero]; dsimp only [times];grobner

def product (x : Fin 84→Rat) : Q2 :=
  times (times (5521,-3576) (cell x 5,cell x 6)) (cell x 25,cell x 26)

theorem ratio677 (x : Fin 84→Rat) (z0 : atWire x 294=0) (z1 : atWire x 305=0) :
    atWire x 677 = linearFactor x * (product x).1 := by
  simp only [e677,e676,e672,e671,e669,e668,e664,e663,e659,e658,e654,e653,e651,e650,e646,e645,e641,e640,e635,e634,e632,e631,e626,e625,e620,e619,e614,e613,e611,e610,e605,e604,e599,e598,e593,e592,e590,e589,e584,e583,e578,e577,e572,e571,e569,e568,e563,e562,e557,e556,e553,e552,e550,e549,e546,e545,e542,e541,e538,e537,e535,e534,e531,e530,e529,e528,e527,e526,e525,e524,e523,e522,e521,e520,e519,e518,e517,e467,e466,e465,e301,e25,e24,e5,e4,z0,z1,Rat.zero_mul,Rat.mul_zero,Rat.zero_add,Rat.add_zero,linearFactor,product,times]
  grobner

theorem ratio782 (x : Fin 84→Rat) (z0 : atWire x 294=0) (z1 : atWire x 305=0) :
    atWire x 782 = linearFactor x * (product x).2 := by
  simp only [e782,e781,e780,e779,e777,e776,e775,e774,e770,e769,e768,e767,e765,e764,e763,e762,e758,e757,e756,e755,e753,e752,e751,e750,e747,e746,e745,e744,e742,e741,e740,e739,e736,e735,e734,e733,e731,e730,e729,e728,e723,e722,e721,e720,e718,e717,e716,e715,e710,e709,e708,e707,e705,e704,e703,e702,e699,e698,e697,e696,e694,e693,e692,e691,e690,e689,e688,e687,e686,e685,e684,e683,e682,e681,e680,e523,e518,e466,e465,e464,e301,e25,e24,e5,e4,z0,z1,Rat.zero_mul,Rat.mul_zero,Rat.zero_add,Rat.add_zero,linearFactor,product,times]
  grobner

end AnchorCollision
