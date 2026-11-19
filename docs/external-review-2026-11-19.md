# External review of z-in-q-lean at `de33a32` (19 November 2026)

This review was made at the request of Jack McCarthy (Deicyde/diophantine-z-q), with AI assistance (Claude Code). It reads the source at commit `de33a32` and the kernel dependency at `2358394`. Nothing was built, and no mathematician has checked these findings. Corrections are welcome.

**Summary.** The qualitative theorem is a sound conditional result. Its target is stated correctly, the deduction uses exactly the twelve listed hypotheses, and none of them was found false or vacuous. Hypothesis 5 now has a confirmed printed source (below). The main open points are the constant in hypothesis 100, the Jacobian supplied by NYLL, and the absence of an automated build of the final theorem.

## What was checked and holds

- **The qualitative target.** `IntegerPolynomial` (`bounded/IntegerPolynomial.lean:15`) states that some integer polynomial in finitely many variables has rational zeros whose first coordinates are exactly the integers. It is a full equivalence over ℚ.
- **The bounded target.** It is the kernel's `ZInQ.FrozenTarget` (`ZInQKernel/Target.lean` at `2358394`).
- **The deduction.** `integer_polynomial_of_arithmetic_geometry` takes exactly the twelve hypotheses of the README, plus the height function `hF`, and every hypothesis is used. Structures such as `QuaternionVariety` are constructed in the proof, not assumed.
- **No escape hatches.** A text scan covered the 147 project modules listed in `geometry/sources.json`, the `bounded/` and `picard/` packages, and the kernel files they import. It found no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `ofReduceBool` or `debug.skipKernelTC`.
- **The free height function is not a loophole.** `VonKanel hF` on its own holds for `hF = 0`. But `HeightComparisons hF` ties `hF` to the stable height of genus-two Jacobians through the Pazuki comparison, and that rules out such choices. This is an argument, not a formal proof.
- **Sources matched against their text:**
  - Laga–Shnidman for 44 and 48 (arXiv 2308.15297v3: Remark 2.12, Lemmas 6.2 and 6.16, Corollary 6.6).
  - Pazuki's constant 96 log 16 for 90 (arXiv 0907.1458, Corollary 1.3).
  - The cluster-picture criterion of Dokchitser–Dokchitser–Maistret–Morgan for 77.
  - Tate's vanishing of H²(G_ℚ, Q̄^×) for 62.
  - Guitart's Proposition 2.10 with Corollary 2.12 for 60. The combination is legitimate: both concern the same variety.

## Hypothesis 5: Tian's Theorem 4.7 is printed as stated

Ye Tian, *Congruent number problem*, Notices of the ICCM 5 (2017), Theorem 4.7, page 58 (attributed to Tian–Yuan–Zhang). For n ≡ 5, 7 (mod 8), it says that 2^(−ρ(n))·𝓛(n) is odd if either of two genus sums is odd. The second sum runs over unordered factorizations n = d₀d₁⋯ with every factor greater than 1, d₀ ≡ 5, 7, d₁ ≡ 2, 3 and all other factors ≡ 1 (mod 8), weighted by ∏ g(dᵢ), where g(d) = #2Cl(ℚ(√−d)).

`TianSecond`, `rowSum`, `factorizations`, `genusNumber` and `Tian47` (`bounded/PublishedGenusRows.lean`, `bounded/TYZFactorizations.lean`, `bounded/TYZIntegerCoefficient.lean`) match this word for word, restricted to n ≡ 5 (mod 8). `PublishedTian47` keeps only the consequence that the order of vanishing is at most 1, so it is weaker than the printed theorem.

Three remarks:

- Theorem 4.7 is stated without proof in a survey. Its proof is Tian–Yuan–Zhang's.
- It is not the statement of Tian–Yuan–Zhang's Theorem 1.2 (arXiv:1411.4728; Theorem 1.4 in Asian J. Math. 21 (2017)), whose literal reading is false.
  - The kernel's note `docs/research/nt-tyz.md` explains why. That theorem's second sum allows d₁ ≡ 1, 2, 3 (mod 8) with every factor greater than 1, and it is odd at n = 26565 and n = 33117, where the rank is 3.
  - The survey's second sum allows only d₁ ≡ 2, 3. For n ≡ 5 (mod 8) it is the (7,3) row alone, so "first sum odd or (7,3) sum odd" is logically equivalent to the reading the kernel calls reading A, the one it judges true.
  - We recomputed both n: the survey's two sums are even, so Theorem 4.7 asserts nothing there, while Theorem 1.2's literal second sum is odd. Class numbers were computed by counting reduced binary quadratic forms. g(d) is odd exactly when the 2-adic valuation of the class number equals the number of prime discriminant factors minus one.
  - The kernel also derives `TYZRow5b`, the (7,3) row with the order of vanishing at most 1, from results of Tian–Yuan–Zhang that it treats as unambiguous (`PropN.tyzRow5b_of_tyzInputs`, `ZInQKernel/RouteK/PropN.lean` on elliotglazer/diophantine-z-q main). Those results remain hypotheses there.
- The kernel's docstring for `Literature.TYZRow5b` (`ZInQKernel/Hypotheses/CR3Literature.lean`) calls this criterion "not a literal published sentence". Tian's survey prints it, so that note is out of date.

## Findings and suggestions, most important first

1. **Hypothesis 100, von Känel's constant.**
   - `vonKanelBound` (`bounded/QualitativeHeight.lean:235`) transcribes inequality (6.7) of von Känel's Theorem 6.2. We could not read the body of the paper to check that transcription, including the definition of v and the conditions under which (6.7) holds.
   - The proof uses the bound only through `vonKanelBound_le`, that is, as ≤ `dimensionCoefficient g` · N²⁴ (`picard/PicardAssembly.lean:223-225`).
   - Stating `VonKanel` in that weaker form, or in the form of the paper's headline bound, would make the theorem independent of the exact constants in (6.7).
2. **No automated build of the final theorem.**
   - The repository has no CI. The root package builds the 31 modules under `Lean/Foundations`, which the final theorem does not import. The final theorem is built only after `geometry/prepare.py` assembles a separate package.
   - A `sorry` in an imported file would be a warning, not an error.
   - The evidence that the build succeeds is `Comparison/geometry-rebuild.json`: a kernel replay accepted with `propext`, `Classical.choice` and `Quot.sound`. The log itself is not in the repository. The same record shows the module-system preview rejected at the import of `GuitartSurfaces`.
   - A workflow that runs `prepare.py`, builds `PicardConclusion` and fails on any `sorry` or extra axiom would close this.
3. **The Jacobian from NYLL.**
   - Hypotheses 44, 48, 77 and 90 are true only if NYLL's `JacobianVarieties.Picard.Unpointed.groupScheme` is the genuine Jacobian.
   - Its defining file (`UnpointedJacobian.lean` at `fe40c03`) has no axiom or `sorry`, but its imports were not checked. If the object were degenerate, hypothesis 48 would be false.
   - Naming the properties of the Jacobian that the proof relies on, or checking NYLL's closure with the same scan, would settle it.
4. **The dashboard's "kernel-checked" count.**
   - `dashboard/README.md` reports 496 of 592 packages with a locally kernel-checked deduction. For most of them, the declarations sit in files that no lakefile or `geometry/sources.json` builds.
   - Of the 2,123 Lean files in the repository, at most 184 belong to a package.
   - `dashboard/lean_source.py` locates declarations without running Lean, so the count records where statements are, not what was checked.
5. **The kernel pin.**
   - `2358394` is not on any branch of elliotglazer/diophantine-z-q. It is the head of the closed pull request elliotglazer/diophantine-z-q#64, reachable only through that pull request's ref, and that repository states no licence.
   - The files your bounded theorem needs from it (`ZInQKernel/Contrib/GaussFE/` and `ZInQKernel/Contrib/HeckeAll/`) are carried byte for byte by the open draft elliotglazer/diophantine-z-q#139.
6. **Smaller points:**
   - Hypothesis 57 appears to follow from the others by elementary algebra: the multiplier is central, the cocycle identity follows by associativity, and c(1,1) = 1 from the canonical isomorphism. If so, it could be proved and dropped from the list.
   - Blueprint entry 47 (`PrymCoordinates`) is counted among the 83 proved implications, but `PicardConclusion` does not import it. It supports the reading of hypothesis 48 rather than the deduction.
   - 46 module names occur in more than one directory. In five of them the copies differ slightly, among them `bounded/PublishedGenusRows.lean` (built) and `Lean/Lemmas/ordinary-fibre-bridge/rank/PublishedGenusRows.lean` (not built, with a different import). The build selects by path, so this does not affect the proof, but it makes the source harder to read.
   - Hypothesis 77 cites Dokchitser–Dokchitser–Maistret–Morgan as Theorem 1.9(5). In the arXiv version the criterion is Theorem 1.8(5). The published numbering was not checked.
   - Hypothesis 6 cites Gross–Zagier and Breuil–Conrad–Diamond–Taylor. Passing to a point of infinite order also needs an auxiliary twist with nonvanishing central value (Bump–Friedberg–Hoffstein or Murty–Murty), which the kernel's docstring cites.

## Not checked

- Any build.
- The printed texts of Gross–Zagier, Milne, Guitart (published version), Ritzenthaler–Romagny and von Känel (Forum of Mathematics, Sigma 9 (2021) e39), which were available to us only as PDFs.
- The code of NYLL and of the Tau Ceti files fetched by `prepare.py`.
- The hypothesis `SixContactMin` of the bounded theorem, which is shared with diophantine-z-q and tracked there.
